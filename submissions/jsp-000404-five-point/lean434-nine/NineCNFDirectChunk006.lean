import NineTheoryTrial

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineCNFDirectTrial

theorem clause8222 (t x02 x07 x27 : ℝ) (h : (((x02 ≤ x07) ∧ (x07 ≤ x27) ∧ ((x27 - x02) ≥ 1) ∧ ((x07 - x02) ≤ (t - 1)) ∧ ((x27 - x07) ≤ (t - 1))) ∨ ((x27 ≤ x07) ∧ (x07 ≤ x02) ∧ ((x02 - x27) ≥ 1) ∧ ((x02 - x07) ≤ (t - 1)) ∧ ((x07 - x27) ≤ (t - 1))))) : (((x27 - x07) ≤ (t - 1)) ∨ ((x07 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8230 (t x36 x38 x68 : ℝ) : (((x36 + ((-1) * x68)) ≥ 1) ∨ ((x38 + ((-1) * x68)) ≤ 0) ∨ (¬ (x36 ≤ x38)) ∨ (¬ (x38 ≤ x68)) ∨ (¬ ((x68 - x36) ≥ 1)) ∨ (¬ ((x38 - x36) ≤ (t - 1))) ∨ (¬ ((x68 - x38) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x38 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th576 t x36 x38 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8233 (t x36 x38 x68 : ℝ) : (((x36 + ((-1) * x68)) ≤ (-1)) ∨ ((x38 + ((-1) * x68)) ≥ 0) ∨ (¬ (x36 ≤ x38)) ∨ (¬ (x38 ≤ x68)) ∨ (¬ ((x68 - x36) ≥ 1)) ∨ (¬ ((x38 - x36) ≤ (t - 1))) ∨ (¬ ((x68 - x38) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 + ((-1) * x68)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x38 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th576 t x36 x38 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8234 (t x36 x38 x68 : ℝ) : (((x36 + ((-1) * x68)) ≤ (-1)) ∨ ((x36 + ((-1) * x38)) ≥ 0) ∨ (¬ (x36 ≤ x38)) ∨ (¬ (x38 ≤ x68)) ∨ (¬ ((x68 - x36) ≥ 1)) ∨ (¬ ((x38 - x36) ≤ (t - 1))) ∨ (¬ ((x68 - x38) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 + ((-1) * x38)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x38 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th576 t x36 x38 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8235 (t x36 x38 x68 : ℝ) : (((x36 + ((-1) * x68)) ≤ (-1)) ∨ ((x36 + ((-1) * x68)) ≥ 1) ∨ (¬ (x36 ≤ x38)) ∨ (¬ (x38 ≤ x68)) ∨ (¬ ((x68 - x36) ≥ 1)) ∨ (¬ ((x38 - x36) ≤ (t - 1))) ∨ (¬ ((x68 - x38) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x38 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th576 t x36 x38 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8236 (t x36 x38 x68 : ℝ) : (((x36 + ((-1) * x68)) ≤ (-1)) ∨ ((t + ((-1) * x36) + x38) ≥ 1) ∨ (¬ (x36 ≤ x38)) ∨ (¬ (x38 ≤ x68)) ∨ (¬ ((x68 - x36) ≥ 1)) ∨ (¬ ((x38 - x36) ≤ (t - 1))) ∨ (¬ ((x68 - x38) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x36) + x38) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x38 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th576 t x36 x38 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8240 (t x36 x38 x68 : ℝ) : (((x36 + ((-1) * x68)) ≥ 1) ∨ ((t + x36 + ((-1) * x38)) ≥ 1) ∨ (¬ (x36 ≤ x38)) ∨ (¬ (x38 ≤ x68)) ∨ (¬ ((x68 - x36) ≥ 1)) ∨ (¬ ((x38 - x36) ≤ (t - 1))) ∨ (¬ ((x68 - x38) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x36 + ((-1) * x38)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x38 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th576 t x36 x38 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8245 (t x36 x38 x68 : ℝ) : (((x36 + ((-1) * x68)) ≥ 1) ∨ ((t + x38 + ((-1) * x68)) ≥ 1) ∨ (¬ (x36 ≤ x38)) ∨ (¬ (x38 ≤ x68)) ∨ (¬ ((x68 - x36) ≥ 1)) ∨ (¬ ((x38 - x36) ≤ (t - 1))) ∨ (¬ ((x68 - x38) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x38 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x38 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th576 t x36 x38 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8255 (t x36 x38 x68 : ℝ) : (((x36 + ((-1) * x68)) ≥ 1) ∨ ((x38 + ((-1) * x68)) ≤ 0) ∨ (¬ (x68 ≤ x38)) ∨ (¬ (x38 ≤ x36)) ∨ (¬ ((x36 - x68) ≥ 1)) ∨ (¬ ((x36 - x38) ≤ (t - 1))) ∨ (¬ ((x38 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x38 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th576 t x36 x38 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8258 (t x36 x38 x68 : ℝ) : (((x36 + ((-1) * x68)) ≤ (-1)) ∨ ((x38 + ((-1) * x68)) ≥ 0) ∨ (¬ (x68 ≤ x38)) ∨ (¬ (x38 ≤ x36)) ∨ (¬ ((x36 - x68) ≥ 1)) ∨ (¬ ((x36 - x38) ≤ (t - 1))) ∨ (¬ ((x38 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 + ((-1) * x68)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x38 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th576 t x36 x38 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8259 (t x36 x38 x68 : ℝ) : (((x36 + ((-1) * x68)) ≤ (-1)) ∨ ((x36 + ((-1) * x38)) ≥ 0) ∨ (¬ (x68 ≤ x38)) ∨ (¬ (x38 ≤ x36)) ∨ (¬ ((x36 - x68) ≥ 1)) ∨ (¬ ((x36 - x38) ≤ (t - 1))) ∨ (¬ ((x38 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 + ((-1) * x38)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x38 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th576 t x36 x38 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8260 (t x36 x38 x68 : ℝ) : (((x36 + ((-1) * x68)) ≤ (-1)) ∨ ((x36 + ((-1) * x68)) ≥ 1) ∨ (¬ (x68 ≤ x38)) ∨ (¬ (x38 ≤ x36)) ∨ (¬ ((x36 - x68) ≥ 1)) ∨ (¬ ((x36 - x38) ≤ (t - 1))) ∨ (¬ ((x38 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x38 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th576 t x36 x38 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8261 (t x36 x38 x68 : ℝ) : (((x36 + ((-1) * x68)) ≤ (-1)) ∨ ((t + ((-1) * x36) + x38) ≥ 1) ∨ (¬ (x68 ≤ x38)) ∨ (¬ (x38 ≤ x36)) ∨ (¬ ((x36 - x68) ≥ 1)) ∨ (¬ ((x36 - x38) ≤ (t - 1))) ∨ (¬ ((x38 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x36) + x38) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x38 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th576 t x36 x38 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8265 (t x36 x38 x68 : ℝ) : (((x36 + ((-1) * x68)) ≥ 1) ∨ ((t + x36 + ((-1) * x38)) ≥ 1) ∨ (¬ (x68 ≤ x38)) ∨ (¬ (x38 ≤ x36)) ∨ (¬ ((x36 - x68) ≥ 1)) ∨ (¬ ((x36 - x38) ≤ (t - 1))) ∨ (¬ ((x38 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x36 + ((-1) * x38)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x38 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th576 t x36 x38 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8270 (t x36 x38 x68 : ℝ) : (((x36 + ((-1) * x68)) ≥ 1) ∨ ((t + x38 + ((-1) * x68)) ≥ 1) ∨ (¬ (x68 ≤ x38)) ∨ (¬ (x38 ≤ x36)) ∨ (¬ ((x36 - x68) ≥ 1)) ∨ (¬ ((x36 - x38) ≤ (t - 1))) ∨ (¬ ((x38 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x38 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x38 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th576 t x36 x38 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8323 (t x36 x38 x68 : ℝ) (h : (((x36 ≤ x38) ∧ (x38 ≤ x68) ∧ ((x68 - x36) ≥ 1) ∧ ((x38 - x36) ≤ (t - 1)) ∧ ((x68 - x38) ≤ (t - 1))) ∨ ((x68 ≤ x38) ∧ (x38 ≤ x36) ∧ ((x36 - x68) ≥ 1) ∧ ((x36 - x38) ≤ (t - 1)) ∧ ((x38 - x68) ≤ (t - 1))))) : ((x36 ≤ x38) ∨ (x68 ≤ x38)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x36 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x38) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8324 (t x36 x38 x68 : ℝ) (h : (((x36 ≤ x38) ∧ (x38 ≤ x68) ∧ ((x68 - x36) ≥ 1) ∧ ((x38 - x36) ≤ (t - 1)) ∧ ((x68 - x38) ≤ (t - 1))) ∨ ((x68 ≤ x38) ∧ (x38 ≤ x36) ∧ ((x36 - x68) ≥ 1) ∧ ((x36 - x38) ≤ (t - 1)) ∧ ((x38 - x68) ≤ (t - 1))))) : ((x36 ≤ x38) ∨ (x38 ≤ x36)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x36 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x36) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8325 (t x36 x38 x68 : ℝ) (h : (((x36 ≤ x38) ∧ (x38 ≤ x68) ∧ ((x68 - x36) ≥ 1) ∧ ((x38 - x36) ≤ (t - 1)) ∧ ((x68 - x38) ≤ (t - 1))) ∨ ((x68 ≤ x38) ∧ (x38 ≤ x36) ∧ ((x36 - x68) ≥ 1) ∧ ((x36 - x38) ≤ (t - 1)) ∧ ((x38 - x68) ≤ (t - 1))))) : ((x36 ≤ x38) ∨ ((x36 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x36 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8326 (t x36 x38 x68 : ℝ) (h : (((x36 ≤ x38) ∧ (x38 ≤ x68) ∧ ((x68 - x36) ≥ 1) ∧ ((x38 - x36) ≤ (t - 1)) ∧ ((x68 - x38) ≤ (t - 1))) ∨ ((x68 ≤ x38) ∧ (x38 ≤ x36) ∧ ((x36 - x68) ≥ 1) ∧ ((x36 - x38) ≤ (t - 1)) ∧ ((x38 - x68) ≤ (t - 1))))) : ((x36 ≤ x38) ∨ ((x36 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x36 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8327 (t x36 x38 x68 : ℝ) (h : (((x36 ≤ x38) ∧ (x38 ≤ x68) ∧ ((x68 - x36) ≥ 1) ∧ ((x38 - x36) ≤ (t - 1)) ∧ ((x68 - x38) ≤ (t - 1))) ∨ ((x68 ≤ x38) ∧ (x38 ≤ x36) ∧ ((x36 - x68) ≥ 1) ∧ ((x36 - x38) ≤ (t - 1)) ∧ ((x38 - x68) ≤ (t - 1))))) : ((x36 ≤ x38) ∨ ((x38 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x36 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8328 (t x36 x38 x68 : ℝ) (h : (((x36 ≤ x38) ∧ (x38 ≤ x68) ∧ ((x68 - x36) ≥ 1) ∧ ((x38 - x36) ≤ (t - 1)) ∧ ((x68 - x38) ≤ (t - 1))) ∨ ((x68 ≤ x38) ∧ (x38 ≤ x36) ∧ ((x36 - x68) ≥ 1) ∧ ((x36 - x38) ≤ (t - 1)) ∧ ((x38 - x68) ≤ (t - 1))))) : ((x38 ≤ x68) ∨ (x68 ≤ x38)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x38 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x38) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8329 (t x36 x38 x68 : ℝ) (h : (((x36 ≤ x38) ∧ (x38 ≤ x68) ∧ ((x68 - x36) ≥ 1) ∧ ((x38 - x36) ≤ (t - 1)) ∧ ((x68 - x38) ≤ (t - 1))) ∨ ((x68 ≤ x38) ∧ (x38 ≤ x36) ∧ ((x36 - x68) ≥ 1) ∧ ((x36 - x38) ≤ (t - 1)) ∧ ((x38 - x68) ≤ (t - 1))))) : ((x38 ≤ x68) ∨ (x38 ≤ x36)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x38 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x36) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8330 (t x36 x38 x68 : ℝ) (h : (((x36 ≤ x38) ∧ (x38 ≤ x68) ∧ ((x68 - x36) ≥ 1) ∧ ((x38 - x36) ≤ (t - 1)) ∧ ((x68 - x38) ≤ (t - 1))) ∨ ((x68 ≤ x38) ∧ (x38 ≤ x36) ∧ ((x36 - x68) ≥ 1) ∧ ((x36 - x38) ≤ (t - 1)) ∧ ((x38 - x68) ≤ (t - 1))))) : ((x38 ≤ x68) ∨ ((x36 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x38 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8331 (t x36 x38 x68 : ℝ) (h : (((x36 ≤ x38) ∧ (x38 ≤ x68) ∧ ((x68 - x36) ≥ 1) ∧ ((x38 - x36) ≤ (t - 1)) ∧ ((x68 - x38) ≤ (t - 1))) ∨ ((x68 ≤ x38) ∧ (x38 ≤ x36) ∧ ((x36 - x68) ≥ 1) ∧ ((x36 - x38) ≤ (t - 1)) ∧ ((x38 - x68) ≤ (t - 1))))) : ((x38 ≤ x68) ∨ ((x36 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x38 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8332 (t x36 x38 x68 : ℝ) (h : (((x36 ≤ x38) ∧ (x38 ≤ x68) ∧ ((x68 - x36) ≥ 1) ∧ ((x38 - x36) ≤ (t - 1)) ∧ ((x68 - x38) ≤ (t - 1))) ∨ ((x68 ≤ x38) ∧ (x38 ≤ x36) ∧ ((x36 - x68) ≥ 1) ∧ ((x36 - x38) ≤ (t - 1)) ∧ ((x38 - x68) ≤ (t - 1))))) : ((x38 ≤ x68) ∨ ((x38 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x38 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8333 (t x36 x38 x68 : ℝ) (h : (((x36 ≤ x38) ∧ (x38 ≤ x68) ∧ ((x68 - x36) ≥ 1) ∧ ((x38 - x36) ≤ (t - 1)) ∧ ((x68 - x38) ≤ (t - 1))) ∨ ((x68 ≤ x38) ∧ (x38 ≤ x36) ∧ ((x36 - x68) ≥ 1) ∧ ((x36 - x38) ≤ (t - 1)) ∧ ((x38 - x68) ≤ (t - 1))))) : (((x68 - x36) ≥ 1) ∨ (x68 ≤ x38)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x36) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x38) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8334 (t x36 x38 x68 : ℝ) (h : (((x36 ≤ x38) ∧ (x38 ≤ x68) ∧ ((x68 - x36) ≥ 1) ∧ ((x38 - x36) ≤ (t - 1)) ∧ ((x68 - x38) ≤ (t - 1))) ∨ ((x68 ≤ x38) ∧ (x38 ≤ x36) ∧ ((x36 - x68) ≥ 1) ∧ ((x36 - x38) ≤ (t - 1)) ∧ ((x38 - x68) ≤ (t - 1))))) : (((x68 - x36) ≥ 1) ∨ (x38 ≤ x36)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x36) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x36) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8335 (t x36 x38 x68 : ℝ) (h : (((x36 ≤ x38) ∧ (x38 ≤ x68) ∧ ((x68 - x36) ≥ 1) ∧ ((x38 - x36) ≤ (t - 1)) ∧ ((x68 - x38) ≤ (t - 1))) ∨ ((x68 ≤ x38) ∧ (x38 ≤ x36) ∧ ((x36 - x68) ≥ 1) ∧ ((x36 - x38) ≤ (t - 1)) ∧ ((x38 - x68) ≤ (t - 1))))) : (((x68 - x36) ≥ 1) ∨ ((x36 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x36) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8336 (t x36 x38 x68 : ℝ) (h : (((x36 ≤ x38) ∧ (x38 ≤ x68) ∧ ((x68 - x36) ≥ 1) ∧ ((x38 - x36) ≤ (t - 1)) ∧ ((x68 - x38) ≤ (t - 1))) ∨ ((x68 ≤ x38) ∧ (x38 ≤ x36) ∧ ((x36 - x68) ≥ 1) ∧ ((x36 - x38) ≤ (t - 1)) ∧ ((x38 - x68) ≤ (t - 1))))) : (((x68 - x36) ≥ 1) ∨ ((x36 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x36) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8337 (t x36 x38 x68 : ℝ) (h : (((x36 ≤ x38) ∧ (x38 ≤ x68) ∧ ((x68 - x36) ≥ 1) ∧ ((x38 - x36) ≤ (t - 1)) ∧ ((x68 - x38) ≤ (t - 1))) ∨ ((x68 ≤ x38) ∧ (x38 ≤ x36) ∧ ((x36 - x68) ≥ 1) ∧ ((x36 - x38) ≤ (t - 1)) ∧ ((x38 - x68) ≤ (t - 1))))) : (((x68 - x36) ≥ 1) ∨ ((x38 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x36) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8338 (t x36 x38 x68 : ℝ) (h : (((x36 ≤ x38) ∧ (x38 ≤ x68) ∧ ((x68 - x36) ≥ 1) ∧ ((x38 - x36) ≤ (t - 1)) ∧ ((x68 - x38) ≤ (t - 1))) ∨ ((x68 ≤ x38) ∧ (x38 ≤ x36) ∧ ((x36 - x68) ≥ 1) ∧ ((x36 - x38) ≤ (t - 1)) ∧ ((x38 - x68) ≤ (t - 1))))) : (((x38 - x36) ≤ (t - 1)) ∨ (x68 ≤ x38)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x36) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x38) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8339 (t x36 x38 x68 : ℝ) (h : (((x36 ≤ x38) ∧ (x38 ≤ x68) ∧ ((x68 - x36) ≥ 1) ∧ ((x38 - x36) ≤ (t - 1)) ∧ ((x68 - x38) ≤ (t - 1))) ∨ ((x68 ≤ x38) ∧ (x38 ≤ x36) ∧ ((x36 - x68) ≥ 1) ∧ ((x36 - x38) ≤ (t - 1)) ∧ ((x38 - x68) ≤ (t - 1))))) : (((x38 - x36) ≤ (t - 1)) ∨ (x38 ≤ x36)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x36) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x36) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8340 (t x36 x38 x68 : ℝ) (h : (((x36 ≤ x38) ∧ (x38 ≤ x68) ∧ ((x68 - x36) ≥ 1) ∧ ((x38 - x36) ≤ (t - 1)) ∧ ((x68 - x38) ≤ (t - 1))) ∨ ((x68 ≤ x38) ∧ (x38 ≤ x36) ∧ ((x36 - x68) ≥ 1) ∧ ((x36 - x38) ≤ (t - 1)) ∧ ((x38 - x68) ≤ (t - 1))))) : (((x38 - x36) ≤ (t - 1)) ∨ ((x36 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x36) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8341 (t x36 x38 x68 : ℝ) (h : (((x36 ≤ x38) ∧ (x38 ≤ x68) ∧ ((x68 - x36) ≥ 1) ∧ ((x38 - x36) ≤ (t - 1)) ∧ ((x68 - x38) ≤ (t - 1))) ∨ ((x68 ≤ x38) ∧ (x38 ≤ x36) ∧ ((x36 - x68) ≥ 1) ∧ ((x36 - x38) ≤ (t - 1)) ∧ ((x38 - x68) ≤ (t - 1))))) : (((x38 - x36) ≤ (t - 1)) ∨ ((x36 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x36) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8342 (t x36 x38 x68 : ℝ) (h : (((x36 ≤ x38) ∧ (x38 ≤ x68) ∧ ((x68 - x36) ≥ 1) ∧ ((x38 - x36) ≤ (t - 1)) ∧ ((x68 - x38) ≤ (t - 1))) ∨ ((x68 ≤ x38) ∧ (x38 ≤ x36) ∧ ((x36 - x68) ≥ 1) ∧ ((x36 - x38) ≤ (t - 1)) ∧ ((x38 - x68) ≤ (t - 1))))) : (((x38 - x36) ≤ (t - 1)) ∨ ((x38 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x36) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8343 (t x36 x38 x68 : ℝ) (h : (((x36 ≤ x38) ∧ (x38 ≤ x68) ∧ ((x68 - x36) ≥ 1) ∧ ((x38 - x36) ≤ (t - 1)) ∧ ((x68 - x38) ≤ (t - 1))) ∨ ((x68 ≤ x38) ∧ (x38 ≤ x36) ∧ ((x36 - x68) ≥ 1) ∧ ((x36 - x38) ≤ (t - 1)) ∧ ((x38 - x68) ≤ (t - 1))))) : (((x68 - x38) ≤ (t - 1)) ∨ (x68 ≤ x38)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x38) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x38) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8344 (t x36 x38 x68 : ℝ) (h : (((x36 ≤ x38) ∧ (x38 ≤ x68) ∧ ((x68 - x36) ≥ 1) ∧ ((x38 - x36) ≤ (t - 1)) ∧ ((x68 - x38) ≤ (t - 1))) ∨ ((x68 ≤ x38) ∧ (x38 ≤ x36) ∧ ((x36 - x68) ≥ 1) ∧ ((x36 - x38) ≤ (t - 1)) ∧ ((x38 - x68) ≤ (t - 1))))) : (((x68 - x38) ≤ (t - 1)) ∨ (x38 ≤ x36)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x38) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x36) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8345 (t x36 x38 x68 : ℝ) (h : (((x36 ≤ x38) ∧ (x38 ≤ x68) ∧ ((x68 - x36) ≥ 1) ∧ ((x38 - x36) ≤ (t - 1)) ∧ ((x68 - x38) ≤ (t - 1))) ∨ ((x68 ≤ x38) ∧ (x38 ≤ x36) ∧ ((x36 - x68) ≥ 1) ∧ ((x36 - x38) ≤ (t - 1)) ∧ ((x38 - x68) ≤ (t - 1))))) : (((x68 - x38) ≤ (t - 1)) ∨ ((x36 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x38) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8346 (t x36 x38 x68 : ℝ) (h : (((x36 ≤ x38) ∧ (x38 ≤ x68) ∧ ((x68 - x36) ≥ 1) ∧ ((x38 - x36) ≤ (t - 1)) ∧ ((x68 - x38) ≤ (t - 1))) ∨ ((x68 ≤ x38) ∧ (x38 ≤ x36) ∧ ((x36 - x68) ≥ 1) ∧ ((x36 - x38) ≤ (t - 1)) ∧ ((x38 - x68) ≤ (t - 1))))) : (((x68 - x38) ≤ (t - 1)) ∨ ((x36 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x38) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8347 (t x36 x38 x68 : ℝ) (h : (((x36 ≤ x38) ∧ (x38 ≤ x68) ∧ ((x68 - x36) ≥ 1) ∧ ((x38 - x36) ≤ (t - 1)) ∧ ((x68 - x38) ≤ (t - 1))) ∨ ((x68 ≤ x38) ∧ (x38 ≤ x36) ∧ ((x36 - x68) ≥ 1) ∧ ((x36 - x38) ≤ (t - 1)) ∧ ((x38 - x68) ≤ (t - 1))))) : (((x68 - x38) ≤ (t - 1)) ∨ ((x38 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x38) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8348 (x78 : ℝ) (h : (x78 ≥ 0)) : ((x78 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x78 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause8351 (t x12 x16 x26 : ℝ) : (((x12 + ((-1) * x16)) ≤ 0) ∨ ((x12 + ((-1) * x26)) ≥ 1) ∨ (¬ (x12 ≤ x16)) ∨ (¬ (x16 ≤ x26)) ∨ (¬ ((x26 - x12) ≥ 1)) ∨ (¬ ((x16 - x12) ≤ (t - 1))) ∨ (¬ ((x26 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x16)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th581 t x12 x16 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8356 (t x12 x16 x26 : ℝ) : (((x16 + ((-1) * x26)) ≤ 0) ∨ ((x12 + ((-1) * x26)) ≥ 1) ∨ (¬ (x12 ≤ x16)) ∨ (¬ (x16 ≤ x26)) ∨ (¬ ((x26 - x12) ≥ 1)) ∨ (¬ ((x16 - x12) ≤ (t - 1))) ∨ (¬ ((x26 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x26)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th581 t x12 x16 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8359 (t x12 x16 x26 : ℝ) : (((x12 + ((-1) * x26)) ≤ (-1)) ∨ ((x16 + ((-1) * x26)) ≥ 0) ∨ (¬ (x12 ≤ x16)) ∨ (¬ (x16 ≤ x26)) ∨ (¬ ((x26 - x12) ≥ 1)) ∨ (¬ ((x16 - x12) ≤ (t - 1))) ∨ (¬ ((x26 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x26)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x26)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th581 t x12 x16 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8360 (t x12 x16 x26 : ℝ) : (((x12 + ((-1) * x26)) ≤ (-1)) ∨ ((x12 + ((-1) * x16)) ≥ 0) ∨ (¬ (x12 ≤ x16)) ∨ (¬ (x16 ≤ x26)) ∨ (¬ ((x26 - x12) ≥ 1)) ∨ (¬ ((x16 - x12) ≤ (t - 1))) ∨ (¬ ((x26 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x26)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x16)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th581 t x12 x16 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8361 (t x12 x16 x26 : ℝ) : (((x12 + ((-1) * x26)) ≤ (-1)) ∨ ((x12 + ((-1) * x26)) ≥ 1) ∨ (¬ (x12 ≤ x16)) ∨ (¬ (x16 ≤ x26)) ∨ (¬ ((x26 - x12) ≥ 1)) ∨ (¬ ((x16 - x12) ≤ (t - 1))) ∨ (¬ ((x26 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x26)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th581 t x12 x16 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8362 (t x12 x16 x26 : ℝ) : (((x12 + ((-1) * x26)) ≤ (-1)) ∨ ((t + ((-1) * x12) + x16) ≥ 1) ∨ (¬ (x12 ≤ x16)) ∨ (¬ (x16 ≤ x26)) ∨ (¬ ((x26 - x12) ≥ 1)) ∨ (¬ ((x16 - x12) ≤ (t - 1))) ∨ (¬ ((x26 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x26)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x12) + x16) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th581 t x12 x16 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8363 (t x12 x16 x26 : ℝ) : (((x12 + ((-1) * x26)) ≤ (-1)) ∨ ((t + ((-1) * x16) + x26) ≥ 1) ∨ (¬ (x12 ≤ x16)) ∨ (¬ (x16 ≤ x26)) ∨ (¬ ((x26 - x12) ≥ 1)) ∨ (¬ ((x16 - x12) ≤ (t - 1))) ∨ (¬ ((x26 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x26)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x16) + x26) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th581 t x12 x16 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8365 (t x12 x16 x26 : ℝ) : (((t + x12 + ((-1) * x16)) ≥ 1) ∨ ((x12 + ((-1) * x16)) ≥ 0) ∨ (¬ (x12 ≤ x16)) ∨ (¬ (x16 ≤ x26)) ∨ (¬ ((x26 - x12) ≥ 1)) ∨ (¬ ((x16 - x12) ≤ (t - 1))) ∨ (¬ ((x26 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x12 + ((-1) * x16)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x16)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th581 t x12 x16 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8366 (t x12 x16 x26 : ℝ) : (((t + x12 + ((-1) * x16)) ≥ 1) ∨ ((x12 + ((-1) * x26)) ≥ 1) ∨ (¬ (x12 ≤ x16)) ∨ (¬ (x16 ≤ x26)) ∨ (¬ ((x26 - x12) ≥ 1)) ∨ (¬ ((x16 - x12) ≤ (t - 1))) ∨ (¬ ((x26 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x12 + ((-1) * x16)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th581 t x12 x16 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8371 (t x12 x16 x26 : ℝ) : (((t + x16 + ((-1) * x26)) ≥ 1) ∨ ((x12 + ((-1) * x26)) ≥ 1) ∨ (¬ (x12 ≤ x16)) ∨ (¬ (x16 ≤ x26)) ∨ (¬ ((x26 - x12) ≥ 1)) ∨ (¬ ((x16 - x12) ≤ (t - 1))) ∨ (¬ ((x26 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x16 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th581 t x12 x16 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8374 (t x12 x16 x26 : ℝ) : (((x12 + ((-1) * x16)) ≤ 0) ∨ ((x16 + ((-1) * x26)) ≥ 0) ∨ (¬ (x26 ≤ x16)) ∨ (¬ (x16 ≤ x12)) ∨ (¬ ((x12 - x26) ≥ 1)) ∨ (¬ ((x12 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x16)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x26)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th581 t x12 x16 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8376 (t x12 x16 x26 : ℝ) : (((x12 + ((-1) * x16)) ≤ 0) ∨ ((x12 + ((-1) * x26)) ≥ 1) ∨ (¬ (x26 ≤ x16)) ∨ (¬ (x16 ≤ x12)) ∨ (¬ ((x12 - x26) ≥ 1)) ∨ (¬ ((x12 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x16)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th581 t x12 x16 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8377 (t x12 x16 x26 : ℝ) : (((x12 + ((-1) * x16)) ≤ 0) ∨ ((t + ((-1) * x12) + x16) ≥ 1) ∨ (¬ (x26 ≤ x16)) ∨ (¬ (x16 ≤ x12)) ∨ (¬ ((x12 - x26) ≥ 1)) ∨ (¬ ((x12 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x16)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x12) + x16) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th581 t x12 x16 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8381 (t x12 x16 x26 : ℝ) : (((x16 + ((-1) * x26)) ≤ 0) ∨ ((x12 + ((-1) * x26)) ≥ 1) ∨ (¬ (x26 ≤ x16)) ∨ (¬ (x16 ≤ x12)) ∨ (¬ ((x12 - x26) ≥ 1)) ∨ (¬ ((x12 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x26)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th581 t x12 x16 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8383 (t x12 x16 x26 : ℝ) : (((x16 + ((-1) * x26)) ≤ 0) ∨ ((t + ((-1) * x16) + x26) ≥ 1) ∨ (¬ (x26 ≤ x16)) ∨ (¬ (x16 ≤ x12)) ∨ (¬ ((x12 - x26) ≥ 1)) ∨ (¬ ((x12 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x26)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x16) + x26) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th581 t x12 x16 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8384 (t x12 x16 x26 : ℝ) : (((x12 + ((-1) * x26)) ≤ (-1)) ∨ ((x16 + ((-1) * x26)) ≥ 0) ∨ (¬ (x26 ≤ x16)) ∨ (¬ (x16 ≤ x12)) ∨ (¬ ((x12 - x26) ≥ 1)) ∨ (¬ ((x12 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x26)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x26)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th581 t x12 x16 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8385 (t x12 x16 x26 : ℝ) : (((x12 + ((-1) * x26)) ≤ (-1)) ∨ ((x12 + ((-1) * x16)) ≥ 0) ∨ (¬ (x26 ≤ x16)) ∨ (¬ (x16 ≤ x12)) ∨ (¬ ((x12 - x26) ≥ 1)) ∨ (¬ ((x12 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x26)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x16)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th581 t x12 x16 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8386 (t x12 x16 x26 : ℝ) : (((x12 + ((-1) * x26)) ≤ (-1)) ∨ ((x12 + ((-1) * x26)) ≥ 1) ∨ (¬ (x26 ≤ x16)) ∨ (¬ (x16 ≤ x12)) ∨ (¬ ((x12 - x26) ≥ 1)) ∨ (¬ ((x12 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x26)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th581 t x12 x16 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8387 (t x12 x16 x26 : ℝ) : (((x12 + ((-1) * x26)) ≤ (-1)) ∨ ((t + ((-1) * x12) + x16) ≥ 1) ∨ (¬ (x26 ≤ x16)) ∨ (¬ (x16 ≤ x12)) ∨ (¬ ((x12 - x26) ≥ 1)) ∨ (¬ ((x12 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x26)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x12) + x16) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th581 t x12 x16 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8391 (t x12 x16 x26 : ℝ) : (((t + x12 + ((-1) * x16)) ≥ 1) ∨ ((x12 + ((-1) * x26)) ≥ 1) ∨ (¬ (x26 ≤ x16)) ∨ (¬ (x16 ≤ x12)) ∨ (¬ ((x12 - x26) ≥ 1)) ∨ (¬ ((x12 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x12 + ((-1) * x16)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th581 t x12 x16 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8396 (t x12 x16 x26 : ℝ) : (((t + x16 + ((-1) * x26)) ≥ 1) ∨ ((x12 + ((-1) * x26)) ≥ 1) ∨ (¬ (x26 ≤ x16)) ∨ (¬ (x16 ≤ x12)) ∨ (¬ ((x12 - x26) ≥ 1)) ∨ (¬ ((x12 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x16 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th581 t x12 x16 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8449 (t x12 x16 x26 : ℝ) (h : (((x12 ≤ x16) ∧ (x16 ≤ x26) ∧ ((x26 - x12) ≥ 1) ∧ ((x16 - x12) ≤ (t - 1)) ∧ ((x26 - x16) ≤ (t - 1))) ∨ ((x26 ≤ x16) ∧ (x16 ≤ x12) ∧ ((x12 - x26) ≥ 1) ∧ ((x12 - x16) ≤ (t - 1)) ∧ ((x16 - x26) ≤ (t - 1))))) : ((x12 ≤ x16) ∨ (x26 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≤ x16) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x26 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8450 (t x12 x16 x26 : ℝ) (h : (((x12 ≤ x16) ∧ (x16 ≤ x26) ∧ ((x26 - x12) ≥ 1) ∧ ((x16 - x12) ≤ (t - 1)) ∧ ((x26 - x16) ≤ (t - 1))) ∨ ((x26 ≤ x16) ∧ (x16 ≤ x12) ∧ ((x12 - x26) ≥ 1) ∧ ((x12 - x16) ≤ (t - 1)) ∧ ((x16 - x26) ≤ (t - 1))))) : ((x12 ≤ x16) ∨ (x16 ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≤ x16) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x16 ≤ x12) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8451 (t x12 x16 x26 : ℝ) (h : (((x12 ≤ x16) ∧ (x16 ≤ x26) ∧ ((x26 - x12) ≥ 1) ∧ ((x16 - x12) ≤ (t - 1)) ∧ ((x26 - x16) ≤ (t - 1))) ∨ ((x26 ≤ x16) ∧ (x16 ≤ x12) ∧ ((x12 - x26) ≥ 1) ∧ ((x12 - x16) ≤ (t - 1)) ∧ ((x16 - x26) ≤ (t - 1))))) : ((x12 ≤ x16) ∨ ((x12 - x26) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≤ x16) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x26) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8452 (t x12 x16 x26 : ℝ) (h : (((x12 ≤ x16) ∧ (x16 ≤ x26) ∧ ((x26 - x12) ≥ 1) ∧ ((x16 - x12) ≤ (t - 1)) ∧ ((x26 - x16) ≤ (t - 1))) ∨ ((x26 ≤ x16) ∧ (x16 ≤ x12) ∧ ((x12 - x26) ≥ 1) ∧ ((x12 - x16) ≤ (t - 1)) ∧ ((x16 - x26) ≤ (t - 1))))) : ((x12 ≤ x16) ∨ ((x12 - x16) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≤ x16) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x16) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8453 (t x12 x16 x26 : ℝ) (h : (((x12 ≤ x16) ∧ (x16 ≤ x26) ∧ ((x26 - x12) ≥ 1) ∧ ((x16 - x12) ≤ (t - 1)) ∧ ((x26 - x16) ≤ (t - 1))) ∨ ((x26 ≤ x16) ∧ (x16 ≤ x12) ∧ ((x12 - x26) ≥ 1) ∧ ((x12 - x16) ≤ (t - 1)) ∧ ((x16 - x26) ≤ (t - 1))))) : ((x12 ≤ x16) ∨ ((x16 - x26) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≤ x16) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x26) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8454 (t x12 x16 x26 : ℝ) (h : (((x12 ≤ x16) ∧ (x16 ≤ x26) ∧ ((x26 - x12) ≥ 1) ∧ ((x16 - x12) ≤ (t - 1)) ∧ ((x26 - x16) ≤ (t - 1))) ∨ ((x26 ≤ x16) ∧ (x16 ≤ x12) ∧ ((x12 - x26) ≥ 1) ∧ ((x12 - x16) ≤ (t - 1)) ∧ ((x16 - x26) ≤ (t - 1))))) : ((x16 ≤ x26) ∨ (x26 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x26) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x26 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8455 (t x12 x16 x26 : ℝ) (h : (((x12 ≤ x16) ∧ (x16 ≤ x26) ∧ ((x26 - x12) ≥ 1) ∧ ((x16 - x12) ≤ (t - 1)) ∧ ((x26 - x16) ≤ (t - 1))) ∨ ((x26 ≤ x16) ∧ (x16 ≤ x12) ∧ ((x12 - x26) ≥ 1) ∧ ((x12 - x16) ≤ (t - 1)) ∧ ((x16 - x26) ≤ (t - 1))))) : ((x16 ≤ x26) ∨ (x16 ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x26) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x16 ≤ x12) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8456 (t x12 x16 x26 : ℝ) (h : (((x12 ≤ x16) ∧ (x16 ≤ x26) ∧ ((x26 - x12) ≥ 1) ∧ ((x16 - x12) ≤ (t - 1)) ∧ ((x26 - x16) ≤ (t - 1))) ∨ ((x26 ≤ x16) ∧ (x16 ≤ x12) ∧ ((x12 - x26) ≥ 1) ∧ ((x12 - x16) ≤ (t - 1)) ∧ ((x16 - x26) ≤ (t - 1))))) : ((x16 ≤ x26) ∨ ((x12 - x26) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x26) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x26) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8457 (t x12 x16 x26 : ℝ) (h : (((x12 ≤ x16) ∧ (x16 ≤ x26) ∧ ((x26 - x12) ≥ 1) ∧ ((x16 - x12) ≤ (t - 1)) ∧ ((x26 - x16) ≤ (t - 1))) ∨ ((x26 ≤ x16) ∧ (x16 ≤ x12) ∧ ((x12 - x26) ≥ 1) ∧ ((x12 - x16) ≤ (t - 1)) ∧ ((x16 - x26) ≤ (t - 1))))) : ((x16 ≤ x26) ∨ ((x12 - x16) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x26) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x16) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8458 (t x12 x16 x26 : ℝ) (h : (((x12 ≤ x16) ∧ (x16 ≤ x26) ∧ ((x26 - x12) ≥ 1) ∧ ((x16 - x12) ≤ (t - 1)) ∧ ((x26 - x16) ≤ (t - 1))) ∨ ((x26 ≤ x16) ∧ (x16 ≤ x12) ∧ ((x12 - x26) ≥ 1) ∧ ((x12 - x16) ≤ (t - 1)) ∧ ((x16 - x26) ≤ (t - 1))))) : ((x16 ≤ x26) ∨ ((x16 - x26) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x26) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x26) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8459 (t x12 x16 x26 : ℝ) (h : (((x12 ≤ x16) ∧ (x16 ≤ x26) ∧ ((x26 - x12) ≥ 1) ∧ ((x16 - x12) ≤ (t - 1)) ∧ ((x26 - x16) ≤ (t - 1))) ∨ ((x26 ≤ x16) ∧ (x16 ≤ x12) ∧ ((x12 - x26) ≥ 1) ∧ ((x12 - x16) ≤ (t - 1)) ∧ ((x16 - x26) ≤ (t - 1))))) : (((x26 - x12) ≥ 1) ∨ (x26 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x12) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x26 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8460 (t x12 x16 x26 : ℝ) (h : (((x12 ≤ x16) ∧ (x16 ≤ x26) ∧ ((x26 - x12) ≥ 1) ∧ ((x16 - x12) ≤ (t - 1)) ∧ ((x26 - x16) ≤ (t - 1))) ∨ ((x26 ≤ x16) ∧ (x16 ≤ x12) ∧ ((x12 - x26) ≥ 1) ∧ ((x12 - x16) ≤ (t - 1)) ∧ ((x16 - x26) ≤ (t - 1))))) : (((x26 - x12) ≥ 1) ∨ (x16 ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x12) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x16 ≤ x12) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8461 (t x12 x16 x26 : ℝ) (h : (((x12 ≤ x16) ∧ (x16 ≤ x26) ∧ ((x26 - x12) ≥ 1) ∧ ((x16 - x12) ≤ (t - 1)) ∧ ((x26 - x16) ≤ (t - 1))) ∨ ((x26 ≤ x16) ∧ (x16 ≤ x12) ∧ ((x12 - x26) ≥ 1) ∧ ((x12 - x16) ≤ (t - 1)) ∧ ((x16 - x26) ≤ (t - 1))))) : (((x26 - x12) ≥ 1) ∨ ((x12 - x26) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x12) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x26) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8462 (t x12 x16 x26 : ℝ) (h : (((x12 ≤ x16) ∧ (x16 ≤ x26) ∧ ((x26 - x12) ≥ 1) ∧ ((x16 - x12) ≤ (t - 1)) ∧ ((x26 - x16) ≤ (t - 1))) ∨ ((x26 ≤ x16) ∧ (x16 ≤ x12) ∧ ((x12 - x26) ≥ 1) ∧ ((x12 - x16) ≤ (t - 1)) ∧ ((x16 - x26) ≤ (t - 1))))) : (((x26 - x12) ≥ 1) ∨ ((x12 - x16) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x12) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x16) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8463 (t x12 x16 x26 : ℝ) (h : (((x12 ≤ x16) ∧ (x16 ≤ x26) ∧ ((x26 - x12) ≥ 1) ∧ ((x16 - x12) ≤ (t - 1)) ∧ ((x26 - x16) ≤ (t - 1))) ∨ ((x26 ≤ x16) ∧ (x16 ≤ x12) ∧ ((x12 - x26) ≥ 1) ∧ ((x12 - x16) ≤ (t - 1)) ∧ ((x16 - x26) ≤ (t - 1))))) : (((x26 - x12) ≥ 1) ∨ ((x16 - x26) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x12) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x26) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8464 (t x12 x16 x26 : ℝ) (h : (((x12 ≤ x16) ∧ (x16 ≤ x26) ∧ ((x26 - x12) ≥ 1) ∧ ((x16 - x12) ≤ (t - 1)) ∧ ((x26 - x16) ≤ (t - 1))) ∨ ((x26 ≤ x16) ∧ (x16 ≤ x12) ∧ ((x12 - x26) ≥ 1) ∧ ((x12 - x16) ≤ (t - 1)) ∧ ((x16 - x26) ≤ (t - 1))))) : (((x16 - x12) ≤ (t - 1)) ∨ (x26 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x12) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x26 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8465 (t x12 x16 x26 : ℝ) (h : (((x12 ≤ x16) ∧ (x16 ≤ x26) ∧ ((x26 - x12) ≥ 1) ∧ ((x16 - x12) ≤ (t - 1)) ∧ ((x26 - x16) ≤ (t - 1))) ∨ ((x26 ≤ x16) ∧ (x16 ≤ x12) ∧ ((x12 - x26) ≥ 1) ∧ ((x12 - x16) ≤ (t - 1)) ∧ ((x16 - x26) ≤ (t - 1))))) : (((x16 - x12) ≤ (t - 1)) ∨ (x16 ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x12) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x16 ≤ x12) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8466 (t x12 x16 x26 : ℝ) (h : (((x12 ≤ x16) ∧ (x16 ≤ x26) ∧ ((x26 - x12) ≥ 1) ∧ ((x16 - x12) ≤ (t - 1)) ∧ ((x26 - x16) ≤ (t - 1))) ∨ ((x26 ≤ x16) ∧ (x16 ≤ x12) ∧ ((x12 - x26) ≥ 1) ∧ ((x12 - x16) ≤ (t - 1)) ∧ ((x16 - x26) ≤ (t - 1))))) : (((x16 - x12) ≤ (t - 1)) ∨ ((x12 - x26) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x12) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x26) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8467 (t x12 x16 x26 : ℝ) (h : (((x12 ≤ x16) ∧ (x16 ≤ x26) ∧ ((x26 - x12) ≥ 1) ∧ ((x16 - x12) ≤ (t - 1)) ∧ ((x26 - x16) ≤ (t - 1))) ∨ ((x26 ≤ x16) ∧ (x16 ≤ x12) ∧ ((x12 - x26) ≥ 1) ∧ ((x12 - x16) ≤ (t - 1)) ∧ ((x16 - x26) ≤ (t - 1))))) : (((x16 - x12) ≤ (t - 1)) ∨ ((x12 - x16) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x12) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x16) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8468 (t x12 x16 x26 : ℝ) (h : (((x12 ≤ x16) ∧ (x16 ≤ x26) ∧ ((x26 - x12) ≥ 1) ∧ ((x16 - x12) ≤ (t - 1)) ∧ ((x26 - x16) ≤ (t - 1))) ∨ ((x26 ≤ x16) ∧ (x16 ≤ x12) ∧ ((x12 - x26) ≥ 1) ∧ ((x12 - x16) ≤ (t - 1)) ∧ ((x16 - x26) ≤ (t - 1))))) : (((x16 - x12) ≤ (t - 1)) ∨ ((x16 - x26) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x12) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x26) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8469 (t x12 x16 x26 : ℝ) (h : (((x12 ≤ x16) ∧ (x16 ≤ x26) ∧ ((x26 - x12) ≥ 1) ∧ ((x16 - x12) ≤ (t - 1)) ∧ ((x26 - x16) ≤ (t - 1))) ∨ ((x26 ≤ x16) ∧ (x16 ≤ x12) ∧ ((x12 - x26) ≥ 1) ∧ ((x12 - x16) ≤ (t - 1)) ∧ ((x16 - x26) ≤ (t - 1))))) : (((x26 - x16) ≤ (t - 1)) ∨ (x26 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x26 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8470 (t x12 x16 x26 : ℝ) (h : (((x12 ≤ x16) ∧ (x16 ≤ x26) ∧ ((x26 - x12) ≥ 1) ∧ ((x16 - x12) ≤ (t - 1)) ∧ ((x26 - x16) ≤ (t - 1))) ∨ ((x26 ≤ x16) ∧ (x16 ≤ x12) ∧ ((x12 - x26) ≥ 1) ∧ ((x12 - x16) ≤ (t - 1)) ∧ ((x16 - x26) ≤ (t - 1))))) : (((x26 - x16) ≤ (t - 1)) ∨ (x16 ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x16 ≤ x12) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8471 (t x12 x16 x26 : ℝ) (h : (((x12 ≤ x16) ∧ (x16 ≤ x26) ∧ ((x26 - x12) ≥ 1) ∧ ((x16 - x12) ≤ (t - 1)) ∧ ((x26 - x16) ≤ (t - 1))) ∨ ((x26 ≤ x16) ∧ (x16 ≤ x12) ∧ ((x12 - x26) ≥ 1) ∧ ((x12 - x16) ≤ (t - 1)) ∧ ((x16 - x26) ≤ (t - 1))))) : (((x26 - x16) ≤ (t - 1)) ∨ ((x12 - x26) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x26) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8472 (t x12 x16 x26 : ℝ) (h : (((x12 ≤ x16) ∧ (x16 ≤ x26) ∧ ((x26 - x12) ≥ 1) ∧ ((x16 - x12) ≤ (t - 1)) ∧ ((x26 - x16) ≤ (t - 1))) ∨ ((x26 ≤ x16) ∧ (x16 ≤ x12) ∧ ((x12 - x26) ≥ 1) ∧ ((x12 - x16) ≤ (t - 1)) ∧ ((x16 - x26) ≤ (t - 1))))) : (((x26 - x16) ≤ (t - 1)) ∨ ((x12 - x16) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x16) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8473 (t x12 x16 x26 : ℝ) (h : (((x12 ≤ x16) ∧ (x16 ≤ x26) ∧ ((x26 - x12) ≥ 1) ∧ ((x16 - x12) ≤ (t - 1)) ∧ ((x26 - x16) ≤ (t - 1))) ∨ ((x26 ≤ x16) ∧ (x16 ≤ x12) ∧ ((x12 - x26) ≥ 1) ∧ ((x12 - x16) ≤ (t - 1)) ∧ ((x16 - x26) ≤ (t - 1))))) : (((x26 - x16) ≤ (t - 1)) ∨ ((x16 - x26) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x26) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8476 (t x07 x08 x78 : ℝ) : (((x07 + ((-1) * x78)) ≥ 1) ∨ ((x07 + ((-1) * x08)) ≤ 0) ∨ (¬ (x07 ≤ x08)) ∨ (¬ (x08 ≤ x78)) ∨ (¬ ((x78 - x07) ≥ 1)) ∨ (¬ ((x08 - x07) ≤ (t - 1))) ∨ (¬ ((x78 - x08) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x08)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x07 ≤ x08) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x08 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x07) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x08 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x08) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th586 t x07 x08 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8481 (t x07 x08 x78 : ℝ) : (((x07 + ((-1) * x78)) ≥ 1) ∨ ((x08 + ((-1) * x78)) ≤ 0) ∨ (¬ (x07 ≤ x08)) ∨ (¬ (x08 ≤ x78)) ∨ (¬ ((x78 - x07) ≥ 1)) ∨ (¬ ((x08 - x07) ≤ (t - 1))) ∨ (¬ ((x78 - x08) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x07 ≤ x08) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x08 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x07) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x08 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x08) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th586 t x07 x08 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8486 (t x07 x08 x78 : ℝ) : (((x07 + ((-1) * x78)) ≥ 1) ∨ ((x07 + ((-1) * x78)) ≤ (-1)) ∨ (¬ (x07 ≤ x08)) ∨ (¬ (x08 ≤ x78)) ∨ (¬ ((x78 - x07) ≥ 1)) ∨ (¬ ((x08 - x07) ≤ (t - 1))) ∨ (¬ ((x78 - x08) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x07 ≤ x08) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x08 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x07) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x08 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x08) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th586 t x07 x08 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8501 (t x07 x08 x78 : ℝ) : (((x07 + ((-1) * x78)) ≥ 1) ∨ ((x07 + ((-1) * x08)) ≤ 0) ∨ (¬ (x78 ≤ x08)) ∨ (¬ (x08 ≤ x07)) ∨ (¬ ((x07 - x78) ≥ 1)) ∨ (¬ ((x07 - x08) ≤ (t - 1))) ∨ (¬ ((x08 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x08)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x08) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x08 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x07 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x08) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x08 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th586 t x07 x08 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8506 (t x07 x08 x78 : ℝ) : (((x07 + ((-1) * x78)) ≥ 1) ∨ ((x08 + ((-1) * x78)) ≤ 0) ∨ (¬ (x78 ≤ x08)) ∨ (¬ (x08 ≤ x07)) ∨ (¬ ((x07 - x78) ≥ 1)) ∨ (¬ ((x07 - x08) ≤ (t - 1))) ∨ (¬ ((x08 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x08) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x08 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x07 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x08) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x08 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th586 t x07 x08 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8511 (t x07 x08 x78 : ℝ) : (((x07 + ((-1) * x78)) ≥ 1) ∨ ((x07 + ((-1) * x78)) ≤ (-1)) ∨ (¬ (x78 ≤ x08)) ∨ (¬ (x08 ≤ x07)) ∨ (¬ ((x07 - x78) ≥ 1)) ∨ (¬ ((x07 - x08) ≤ (t - 1))) ∨ (¬ ((x08 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x08) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x08 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x07 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x08) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x08 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th586 t x07 x08 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8574 (t x07 x08 x78 : ℝ) (h : (((x07 ≤ x08) ∧ (x08 ≤ x78) ∧ ((x78 - x07) ≥ 1) ∧ ((x08 - x07) ≤ (t - 1)) ∧ ((x78 - x08) ≤ (t - 1))) ∨ ((x78 ≤ x08) ∧ (x08 ≤ x07) ∧ ((x07 - x78) ≥ 1) ∧ ((x07 - x08) ≤ (t - 1)) ∧ ((x08 - x78) ≤ (t - 1))))) : ((x07 ≤ x08) ∨ (x78 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8575 (t x07 x08 x78 : ℝ) (h : (((x07 ≤ x08) ∧ (x08 ≤ x78) ∧ ((x78 - x07) ≥ 1) ∧ ((x08 - x07) ≤ (t - 1)) ∧ ((x78 - x08) ≤ (t - 1))) ∨ ((x78 ≤ x08) ∧ (x08 ≤ x07) ∧ ((x07 - x78) ≥ 1) ∧ ((x07 - x08) ≤ (t - 1)) ∧ ((x08 - x78) ≤ (t - 1))))) : ((x07 ≤ x08) ∨ (x08 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8576 (t x07 x08 x78 : ℝ) (h : (((x07 ≤ x08) ∧ (x08 ≤ x78) ∧ ((x78 - x07) ≥ 1) ∧ ((x08 - x07) ≤ (t - 1)) ∧ ((x78 - x08) ≤ (t - 1))) ∨ ((x78 ≤ x08) ∧ (x08 ≤ x07) ∧ ((x07 - x78) ≥ 1) ∧ ((x07 - x08) ≤ (t - 1)) ∧ ((x08 - x78) ≤ (t - 1))))) : ((x07 ≤ x08) ∨ ((x07 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8577 (t x07 x08 x78 : ℝ) (h : (((x07 ≤ x08) ∧ (x08 ≤ x78) ∧ ((x78 - x07) ≥ 1) ∧ ((x08 - x07) ≤ (t - 1)) ∧ ((x78 - x08) ≤ (t - 1))) ∨ ((x78 ≤ x08) ∧ (x08 ≤ x07) ∧ ((x07 - x78) ≥ 1) ∧ ((x07 - x08) ≤ (t - 1)) ∧ ((x08 - x78) ≤ (t - 1))))) : ((x07 ≤ x08) ∨ ((x07 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8578 (t x07 x08 x78 : ℝ) (h : (((x07 ≤ x08) ∧ (x08 ≤ x78) ∧ ((x78 - x07) ≥ 1) ∧ ((x08 - x07) ≤ (t - 1)) ∧ ((x78 - x08) ≤ (t - 1))) ∨ ((x78 ≤ x08) ∧ (x08 ≤ x07) ∧ ((x07 - x78) ≥ 1) ∧ ((x07 - x08) ≤ (t - 1)) ∧ ((x08 - x78) ≤ (t - 1))))) : ((x07 ≤ x08) ∨ ((x08 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8579 (t x07 x08 x78 : ℝ) (h : (((x07 ≤ x08) ∧ (x08 ≤ x78) ∧ ((x78 - x07) ≥ 1) ∧ ((x08 - x07) ≤ (t - 1)) ∧ ((x78 - x08) ≤ (t - 1))) ∨ ((x78 ≤ x08) ∧ (x08 ≤ x07) ∧ ((x07 - x78) ≥ 1) ∧ ((x07 - x08) ≤ (t - 1)) ∧ ((x08 - x78) ≤ (t - 1))))) : ((x08 ≤ x78) ∨ (x78 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8580 (t x07 x08 x78 : ℝ) (h : (((x07 ≤ x08) ∧ (x08 ≤ x78) ∧ ((x78 - x07) ≥ 1) ∧ ((x08 - x07) ≤ (t - 1)) ∧ ((x78 - x08) ≤ (t - 1))) ∨ ((x78 ≤ x08) ∧ (x08 ≤ x07) ∧ ((x07 - x78) ≥ 1) ∧ ((x07 - x08) ≤ (t - 1)) ∧ ((x08 - x78) ≤ (t - 1))))) : ((x08 ≤ x78) ∨ (x08 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8581 (t x07 x08 x78 : ℝ) (h : (((x07 ≤ x08) ∧ (x08 ≤ x78) ∧ ((x78 - x07) ≥ 1) ∧ ((x08 - x07) ≤ (t - 1)) ∧ ((x78 - x08) ≤ (t - 1))) ∨ ((x78 ≤ x08) ∧ (x08 ≤ x07) ∧ ((x07 - x78) ≥ 1) ∧ ((x07 - x08) ≤ (t - 1)) ∧ ((x08 - x78) ≤ (t - 1))))) : ((x08 ≤ x78) ∨ ((x07 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8582 (t x07 x08 x78 : ℝ) (h : (((x07 ≤ x08) ∧ (x08 ≤ x78) ∧ ((x78 - x07) ≥ 1) ∧ ((x08 - x07) ≤ (t - 1)) ∧ ((x78 - x08) ≤ (t - 1))) ∨ ((x78 ≤ x08) ∧ (x08 ≤ x07) ∧ ((x07 - x78) ≥ 1) ∧ ((x07 - x08) ≤ (t - 1)) ∧ ((x08 - x78) ≤ (t - 1))))) : ((x08 ≤ x78) ∨ ((x07 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8583 (t x07 x08 x78 : ℝ) (h : (((x07 ≤ x08) ∧ (x08 ≤ x78) ∧ ((x78 - x07) ≥ 1) ∧ ((x08 - x07) ≤ (t - 1)) ∧ ((x78 - x08) ≤ (t - 1))) ∨ ((x78 ≤ x08) ∧ (x08 ≤ x07) ∧ ((x07 - x78) ≥ 1) ∧ ((x07 - x08) ≤ (t - 1)) ∧ ((x08 - x78) ≤ (t - 1))))) : ((x08 ≤ x78) ∨ ((x08 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8584 (t x07 x08 x78 : ℝ) (h : (((x07 ≤ x08) ∧ (x08 ≤ x78) ∧ ((x78 - x07) ≥ 1) ∧ ((x08 - x07) ≤ (t - 1)) ∧ ((x78 - x08) ≤ (t - 1))) ∨ ((x78 ≤ x08) ∧ (x08 ≤ x07) ∧ ((x07 - x78) ≥ 1) ∧ ((x07 - x08) ≤ (t - 1)) ∧ ((x08 - x78) ≤ (t - 1))))) : (((x78 - x07) ≥ 1) ∨ (x78 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x07) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8585 (t x07 x08 x78 : ℝ) (h : (((x07 ≤ x08) ∧ (x08 ≤ x78) ∧ ((x78 - x07) ≥ 1) ∧ ((x08 - x07) ≤ (t - 1)) ∧ ((x78 - x08) ≤ (t - 1))) ∨ ((x78 ≤ x08) ∧ (x08 ≤ x07) ∧ ((x07 - x78) ≥ 1) ∧ ((x07 - x08) ≤ (t - 1)) ∧ ((x08 - x78) ≤ (t - 1))))) : (((x78 - x07) ≥ 1) ∨ (x08 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x07) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8586 (t x07 x08 x78 : ℝ) (h : (((x07 ≤ x08) ∧ (x08 ≤ x78) ∧ ((x78 - x07) ≥ 1) ∧ ((x08 - x07) ≤ (t - 1)) ∧ ((x78 - x08) ≤ (t - 1))) ∨ ((x78 ≤ x08) ∧ (x08 ≤ x07) ∧ ((x07 - x78) ≥ 1) ∧ ((x07 - x08) ≤ (t - 1)) ∧ ((x08 - x78) ≤ (t - 1))))) : (((x78 - x07) ≥ 1) ∨ ((x07 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x07) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8587 (t x07 x08 x78 : ℝ) (h : (((x07 ≤ x08) ∧ (x08 ≤ x78) ∧ ((x78 - x07) ≥ 1) ∧ ((x08 - x07) ≤ (t - 1)) ∧ ((x78 - x08) ≤ (t - 1))) ∨ ((x78 ≤ x08) ∧ (x08 ≤ x07) ∧ ((x07 - x78) ≥ 1) ∧ ((x07 - x08) ≤ (t - 1)) ∧ ((x08 - x78) ≤ (t - 1))))) : (((x78 - x07) ≥ 1) ∨ ((x07 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x07) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8588 (t x07 x08 x78 : ℝ) (h : (((x07 ≤ x08) ∧ (x08 ≤ x78) ∧ ((x78 - x07) ≥ 1) ∧ ((x08 - x07) ≤ (t - 1)) ∧ ((x78 - x08) ≤ (t - 1))) ∨ ((x78 ≤ x08) ∧ (x08 ≤ x07) ∧ ((x07 - x78) ≥ 1) ∧ ((x07 - x08) ≤ (t - 1)) ∧ ((x08 - x78) ≤ (t - 1))))) : (((x78 - x07) ≥ 1) ∨ ((x08 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x07) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8589 (t x07 x08 x78 : ℝ) (h : (((x07 ≤ x08) ∧ (x08 ≤ x78) ∧ ((x78 - x07) ≥ 1) ∧ ((x08 - x07) ≤ (t - 1)) ∧ ((x78 - x08) ≤ (t - 1))) ∨ ((x78 ≤ x08) ∧ (x08 ≤ x07) ∧ ((x07 - x78) ≥ 1) ∧ ((x07 - x08) ≤ (t - 1)) ∧ ((x08 - x78) ≤ (t - 1))))) : (((x08 - x07) ≤ (t - 1)) ∨ (x78 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8590 (t x07 x08 x78 : ℝ) (h : (((x07 ≤ x08) ∧ (x08 ≤ x78) ∧ ((x78 - x07) ≥ 1) ∧ ((x08 - x07) ≤ (t - 1)) ∧ ((x78 - x08) ≤ (t - 1))) ∨ ((x78 ≤ x08) ∧ (x08 ≤ x07) ∧ ((x07 - x78) ≥ 1) ∧ ((x07 - x08) ≤ (t - 1)) ∧ ((x08 - x78) ≤ (t - 1))))) : (((x08 - x07) ≤ (t - 1)) ∨ (x08 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8591 (t x07 x08 x78 : ℝ) (h : (((x07 ≤ x08) ∧ (x08 ≤ x78) ∧ ((x78 - x07) ≥ 1) ∧ ((x08 - x07) ≤ (t - 1)) ∧ ((x78 - x08) ≤ (t - 1))) ∨ ((x78 ≤ x08) ∧ (x08 ≤ x07) ∧ ((x07 - x78) ≥ 1) ∧ ((x07 - x08) ≤ (t - 1)) ∧ ((x08 - x78) ≤ (t - 1))))) : (((x08 - x07) ≤ (t - 1)) ∨ ((x07 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8592 (t x07 x08 x78 : ℝ) (h : (((x07 ≤ x08) ∧ (x08 ≤ x78) ∧ ((x78 - x07) ≥ 1) ∧ ((x08 - x07) ≤ (t - 1)) ∧ ((x78 - x08) ≤ (t - 1))) ∨ ((x78 ≤ x08) ∧ (x08 ≤ x07) ∧ ((x07 - x78) ≥ 1) ∧ ((x07 - x08) ≤ (t - 1)) ∧ ((x08 - x78) ≤ (t - 1))))) : (((x08 - x07) ≤ (t - 1)) ∨ ((x07 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8593 (t x07 x08 x78 : ℝ) (h : (((x07 ≤ x08) ∧ (x08 ≤ x78) ∧ ((x78 - x07) ≥ 1) ∧ ((x08 - x07) ≤ (t - 1)) ∧ ((x78 - x08) ≤ (t - 1))) ∨ ((x78 ≤ x08) ∧ (x08 ≤ x07) ∧ ((x07 - x78) ≥ 1) ∧ ((x07 - x08) ≤ (t - 1)) ∧ ((x08 - x78) ≤ (t - 1))))) : (((x08 - x07) ≤ (t - 1)) ∨ ((x08 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8594 (t x07 x08 x78 : ℝ) (h : (((x07 ≤ x08) ∧ (x08 ≤ x78) ∧ ((x78 - x07) ≥ 1) ∧ ((x08 - x07) ≤ (t - 1)) ∧ ((x78 - x08) ≤ (t - 1))) ∨ ((x78 ≤ x08) ∧ (x08 ≤ x07) ∧ ((x07 - x78) ≥ 1) ∧ ((x07 - x08) ≤ (t - 1)) ∧ ((x08 - x78) ≤ (t - 1))))) : (((x78 - x08) ≤ (t - 1)) ∨ (x78 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8595 (t x07 x08 x78 : ℝ) (h : (((x07 ≤ x08) ∧ (x08 ≤ x78) ∧ ((x78 - x07) ≥ 1) ∧ ((x08 - x07) ≤ (t - 1)) ∧ ((x78 - x08) ≤ (t - 1))) ∨ ((x78 ≤ x08) ∧ (x08 ≤ x07) ∧ ((x07 - x78) ≥ 1) ∧ ((x07 - x08) ≤ (t - 1)) ∧ ((x08 - x78) ≤ (t - 1))))) : (((x78 - x08) ≤ (t - 1)) ∨ (x08 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8596 (t x07 x08 x78 : ℝ) (h : (((x07 ≤ x08) ∧ (x08 ≤ x78) ∧ ((x78 - x07) ≥ 1) ∧ ((x08 - x07) ≤ (t - 1)) ∧ ((x78 - x08) ≤ (t - 1))) ∨ ((x78 ≤ x08) ∧ (x08 ≤ x07) ∧ ((x07 - x78) ≥ 1) ∧ ((x07 - x08) ≤ (t - 1)) ∧ ((x08 - x78) ≤ (t - 1))))) : (((x78 - x08) ≤ (t - 1)) ∨ ((x07 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8597 (t x07 x08 x78 : ℝ) (h : (((x07 ≤ x08) ∧ (x08 ≤ x78) ∧ ((x78 - x07) ≥ 1) ∧ ((x08 - x07) ≤ (t - 1)) ∧ ((x78 - x08) ≤ (t - 1))) ∨ ((x78 ≤ x08) ∧ (x08 ≤ x07) ∧ ((x07 - x78) ≥ 1) ∧ ((x07 - x08) ≤ (t - 1)) ∧ ((x08 - x78) ≤ (t - 1))))) : (((x78 - x08) ≤ (t - 1)) ∨ ((x07 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8598 (t x07 x08 x78 : ℝ) (h : (((x07 ≤ x08) ∧ (x08 ≤ x78) ∧ ((x78 - x07) ≥ 1) ∧ ((x08 - x07) ≤ (t - 1)) ∧ ((x78 - x08) ≤ (t - 1))) ∨ ((x78 ≤ x08) ∧ (x08 ≤ x07) ∧ ((x07 - x78) ≥ 1) ∧ ((x07 - x08) ≤ (t - 1)) ∧ ((x08 - x78) ≤ (t - 1))))) : (((x78 - x08) ≤ (t - 1)) ∨ ((x08 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8599 (t x01 x15 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th588 t x01 x15 x57 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u2 u6)))))))) h

theorem clause8600 (t x01 x17 x35 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ ((t + ((-1) * x35)) ≤ 0) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th589 t x01 x17 x35 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u5 (And.intro u6 (And.intro u0 (And.intro u3 u1)))))))) h

theorem clause8613 (t x17 x18 x78 : ℝ) : (((x17 + ((-1) * x78)) ≤ (-1)) ∨ ((x17 + ((-1) * x78)) ≥ 1) ∨ (¬ (x17 ≤ x18)) ∨ (¬ (x18 ≤ x78)) ∨ (¬ ((x78 - x17) ≥ 1)) ∨ (¬ ((x18 - x17) ≤ (t - 1))) ∨ (¬ ((x78 - x18) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x17 ≤ x18) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x18 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x17) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x18 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x18) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th591 t x17 x18 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8615 (t x17 x18 x78 : ℝ) : (((x17 + ((-1) * x78)) ≤ (-1)) ∨ ((t + ((-1) * x18) + x78) ≥ 1) ∨ (¬ (x17 ≤ x18)) ∨ (¬ (x18 ≤ x78)) ∨ (¬ ((x78 - x17) ≥ 1)) ∨ (¬ ((x18 - x17) ≤ (t - 1))) ∨ (¬ ((x78 - x18) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x18) + x78) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x17 ≤ x18) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x18 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x17) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x18 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x18) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th591 t x17 x18 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8638 (t x17 x18 x78 : ℝ) : (((x17 + ((-1) * x78)) ≤ (-1)) ∨ ((x17 + ((-1) * x78)) ≥ 1) ∨ (¬ (x78 ≤ x18)) ∨ (¬ (x18 ≤ x17)) ∨ (¬ ((x17 - x78) ≥ 1)) ∨ (¬ ((x17 - x18) ≤ (t - 1))) ∨ (¬ ((x18 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x18) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x18 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x17 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x18) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x18 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th591 t x17 x18 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8640 (t x17 x18 x78 : ℝ) : (((x17 + ((-1) * x78)) ≤ (-1)) ∨ ((t + ((-1) * x18) + x78) ≥ 1) ∨ (¬ (x78 ≤ x18)) ∨ (¬ (x18 ≤ x17)) ∨ (¬ ((x17 - x78) ≥ 1)) ∨ (¬ ((x17 - x18) ≤ (t - 1))) ∨ (¬ ((x18 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x18) + x78) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x18) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x18 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x17 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x18) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x18 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th591 t x17 x18 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8701 (t x17 x18 x78 : ℝ) (h : (((x17 ≤ x18) ∧ (x18 ≤ x78) ∧ ((x78 - x17) ≥ 1) ∧ ((x18 - x17) ≤ (t - 1)) ∧ ((x78 - x18) ≤ (t - 1))) ∨ ((x78 ≤ x18) ∧ (x18 ≤ x17) ∧ ((x17 - x78) ≥ 1) ∧ ((x17 - x18) ≤ (t - 1)) ∧ ((x18 - x78) ≤ (t - 1))))) : ((x17 ≤ x18) ∨ (x78 ≤ x18)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x18) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8702 (t x17 x18 x78 : ℝ) (h : (((x17 ≤ x18) ∧ (x18 ≤ x78) ∧ ((x78 - x17) ≥ 1) ∧ ((x18 - x17) ≤ (t - 1)) ∧ ((x78 - x18) ≤ (t - 1))) ∨ ((x78 ≤ x18) ∧ (x18 ≤ x17) ∧ ((x17 - x78) ≥ 1) ∧ ((x17 - x18) ≤ (t - 1)) ∧ ((x18 - x78) ≤ (t - 1))))) : ((x17 ≤ x18) ∨ (x18 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8703 (t x17 x18 x78 : ℝ) (h : (((x17 ≤ x18) ∧ (x18 ≤ x78) ∧ ((x78 - x17) ≥ 1) ∧ ((x18 - x17) ≤ (t - 1)) ∧ ((x78 - x18) ≤ (t - 1))) ∨ ((x78 ≤ x18) ∧ (x18 ≤ x17) ∧ ((x17 - x78) ≥ 1) ∧ ((x17 - x18) ≤ (t - 1)) ∧ ((x18 - x78) ≤ (t - 1))))) : ((x17 ≤ x18) ∨ ((x17 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8704 (t x17 x18 x78 : ℝ) (h : (((x17 ≤ x18) ∧ (x18 ≤ x78) ∧ ((x78 - x17) ≥ 1) ∧ ((x18 - x17) ≤ (t - 1)) ∧ ((x78 - x18) ≤ (t - 1))) ∨ ((x78 ≤ x18) ∧ (x18 ≤ x17) ∧ ((x17 - x78) ≥ 1) ∧ ((x17 - x18) ≤ (t - 1)) ∧ ((x18 - x78) ≤ (t - 1))))) : ((x17 ≤ x18) ∨ ((x17 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8705 (t x17 x18 x78 : ℝ) (h : (((x17 ≤ x18) ∧ (x18 ≤ x78) ∧ ((x78 - x17) ≥ 1) ∧ ((x18 - x17) ≤ (t - 1)) ∧ ((x78 - x18) ≤ (t - 1))) ∨ ((x78 ≤ x18) ∧ (x18 ≤ x17) ∧ ((x17 - x78) ≥ 1) ∧ ((x17 - x18) ≤ (t - 1)) ∧ ((x18 - x78) ≤ (t - 1))))) : ((x17 ≤ x18) ∨ ((x18 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8706 (t x17 x18 x78 : ℝ) (h : (((x17 ≤ x18) ∧ (x18 ≤ x78) ∧ ((x78 - x17) ≥ 1) ∧ ((x18 - x17) ≤ (t - 1)) ∧ ((x78 - x18) ≤ (t - 1))) ∨ ((x78 ≤ x18) ∧ (x18 ≤ x17) ∧ ((x17 - x78) ≥ 1) ∧ ((x17 - x18) ≤ (t - 1)) ∧ ((x18 - x78) ≤ (t - 1))))) : ((x18 ≤ x78) ∨ (x78 ≤ x18)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x18 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x18) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8707 (t x17 x18 x78 : ℝ) (h : (((x17 ≤ x18) ∧ (x18 ≤ x78) ∧ ((x78 - x17) ≥ 1) ∧ ((x18 - x17) ≤ (t - 1)) ∧ ((x78 - x18) ≤ (t - 1))) ∨ ((x78 ≤ x18) ∧ (x18 ≤ x17) ∧ ((x17 - x78) ≥ 1) ∧ ((x17 - x18) ≤ (t - 1)) ∧ ((x18 - x78) ≤ (t - 1))))) : ((x18 ≤ x78) ∨ (x18 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x18 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8708 (t x17 x18 x78 : ℝ) (h : (((x17 ≤ x18) ∧ (x18 ≤ x78) ∧ ((x78 - x17) ≥ 1) ∧ ((x18 - x17) ≤ (t - 1)) ∧ ((x78 - x18) ≤ (t - 1))) ∨ ((x78 ≤ x18) ∧ (x18 ≤ x17) ∧ ((x17 - x78) ≥ 1) ∧ ((x17 - x18) ≤ (t - 1)) ∧ ((x18 - x78) ≤ (t - 1))))) : ((x18 ≤ x78) ∨ ((x17 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x18 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8709 (t x17 x18 x78 : ℝ) (h : (((x17 ≤ x18) ∧ (x18 ≤ x78) ∧ ((x78 - x17) ≥ 1) ∧ ((x18 - x17) ≤ (t - 1)) ∧ ((x78 - x18) ≤ (t - 1))) ∨ ((x78 ≤ x18) ∧ (x18 ≤ x17) ∧ ((x17 - x78) ≥ 1) ∧ ((x17 - x18) ≤ (t - 1)) ∧ ((x18 - x78) ≤ (t - 1))))) : ((x18 ≤ x78) ∨ ((x17 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x18 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8710 (t x17 x18 x78 : ℝ) (h : (((x17 ≤ x18) ∧ (x18 ≤ x78) ∧ ((x78 - x17) ≥ 1) ∧ ((x18 - x17) ≤ (t - 1)) ∧ ((x78 - x18) ≤ (t - 1))) ∨ ((x78 ≤ x18) ∧ (x18 ≤ x17) ∧ ((x17 - x78) ≥ 1) ∧ ((x17 - x18) ≤ (t - 1)) ∧ ((x18 - x78) ≤ (t - 1))))) : ((x18 ≤ x78) ∨ ((x18 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x18 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8711 (t x17 x18 x78 : ℝ) (h : (((x17 ≤ x18) ∧ (x18 ≤ x78) ∧ ((x78 - x17) ≥ 1) ∧ ((x18 - x17) ≤ (t - 1)) ∧ ((x78 - x18) ≤ (t - 1))) ∨ ((x78 ≤ x18) ∧ (x18 ≤ x17) ∧ ((x17 - x78) ≥ 1) ∧ ((x17 - x18) ≤ (t - 1)) ∧ ((x18 - x78) ≤ (t - 1))))) : (((x78 - x17) ≥ 1) ∨ (x78 ≤ x18)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x17) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x18) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8712 (t x17 x18 x78 : ℝ) (h : (((x17 ≤ x18) ∧ (x18 ≤ x78) ∧ ((x78 - x17) ≥ 1) ∧ ((x18 - x17) ≤ (t - 1)) ∧ ((x78 - x18) ≤ (t - 1))) ∨ ((x78 ≤ x18) ∧ (x18 ≤ x17) ∧ ((x17 - x78) ≥ 1) ∧ ((x17 - x18) ≤ (t - 1)) ∧ ((x18 - x78) ≤ (t - 1))))) : (((x78 - x17) ≥ 1) ∨ (x18 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x17) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8713 (t x17 x18 x78 : ℝ) (h : (((x17 ≤ x18) ∧ (x18 ≤ x78) ∧ ((x78 - x17) ≥ 1) ∧ ((x18 - x17) ≤ (t - 1)) ∧ ((x78 - x18) ≤ (t - 1))) ∨ ((x78 ≤ x18) ∧ (x18 ≤ x17) ∧ ((x17 - x78) ≥ 1) ∧ ((x17 - x18) ≤ (t - 1)) ∧ ((x18 - x78) ≤ (t - 1))))) : (((x78 - x17) ≥ 1) ∨ ((x17 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x17) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8714 (t x17 x18 x78 : ℝ) (h : (((x17 ≤ x18) ∧ (x18 ≤ x78) ∧ ((x78 - x17) ≥ 1) ∧ ((x18 - x17) ≤ (t - 1)) ∧ ((x78 - x18) ≤ (t - 1))) ∨ ((x78 ≤ x18) ∧ (x18 ≤ x17) ∧ ((x17 - x78) ≥ 1) ∧ ((x17 - x18) ≤ (t - 1)) ∧ ((x18 - x78) ≤ (t - 1))))) : (((x78 - x17) ≥ 1) ∨ ((x17 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x17) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8715 (t x17 x18 x78 : ℝ) (h : (((x17 ≤ x18) ∧ (x18 ≤ x78) ∧ ((x78 - x17) ≥ 1) ∧ ((x18 - x17) ≤ (t - 1)) ∧ ((x78 - x18) ≤ (t - 1))) ∨ ((x78 ≤ x18) ∧ (x18 ≤ x17) ∧ ((x17 - x78) ≥ 1) ∧ ((x17 - x18) ≤ (t - 1)) ∧ ((x18 - x78) ≤ (t - 1))))) : (((x78 - x17) ≥ 1) ∨ ((x18 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x17) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8716 (t x17 x18 x78 : ℝ) (h : (((x17 ≤ x18) ∧ (x18 ≤ x78) ∧ ((x78 - x17) ≥ 1) ∧ ((x18 - x17) ≤ (t - 1)) ∧ ((x78 - x18) ≤ (t - 1))) ∨ ((x78 ≤ x18) ∧ (x18 ≤ x17) ∧ ((x17 - x78) ≥ 1) ∧ ((x17 - x18) ≤ (t - 1)) ∧ ((x18 - x78) ≤ (t - 1))))) : (((x18 - x17) ≤ (t - 1)) ∨ (x78 ≤ x18)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x18) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8717 (t x17 x18 x78 : ℝ) (h : (((x17 ≤ x18) ∧ (x18 ≤ x78) ∧ ((x78 - x17) ≥ 1) ∧ ((x18 - x17) ≤ (t - 1)) ∧ ((x78 - x18) ≤ (t - 1))) ∨ ((x78 ≤ x18) ∧ (x18 ≤ x17) ∧ ((x17 - x78) ≥ 1) ∧ ((x17 - x18) ≤ (t - 1)) ∧ ((x18 - x78) ≤ (t - 1))))) : (((x18 - x17) ≤ (t - 1)) ∨ (x18 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8718 (t x17 x18 x78 : ℝ) (h : (((x17 ≤ x18) ∧ (x18 ≤ x78) ∧ ((x78 - x17) ≥ 1) ∧ ((x18 - x17) ≤ (t - 1)) ∧ ((x78 - x18) ≤ (t - 1))) ∨ ((x78 ≤ x18) ∧ (x18 ≤ x17) ∧ ((x17 - x78) ≥ 1) ∧ ((x17 - x18) ≤ (t - 1)) ∧ ((x18 - x78) ≤ (t - 1))))) : (((x18 - x17) ≤ (t - 1)) ∨ ((x17 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8719 (t x17 x18 x78 : ℝ) (h : (((x17 ≤ x18) ∧ (x18 ≤ x78) ∧ ((x78 - x17) ≥ 1) ∧ ((x18 - x17) ≤ (t - 1)) ∧ ((x78 - x18) ≤ (t - 1))) ∨ ((x78 ≤ x18) ∧ (x18 ≤ x17) ∧ ((x17 - x78) ≥ 1) ∧ ((x17 - x18) ≤ (t - 1)) ∧ ((x18 - x78) ≤ (t - 1))))) : (((x18 - x17) ≤ (t - 1)) ∨ ((x17 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8720 (t x17 x18 x78 : ℝ) (h : (((x17 ≤ x18) ∧ (x18 ≤ x78) ∧ ((x78 - x17) ≥ 1) ∧ ((x18 - x17) ≤ (t - 1)) ∧ ((x78 - x18) ≤ (t - 1))) ∨ ((x78 ≤ x18) ∧ (x18 ≤ x17) ∧ ((x17 - x78) ≥ 1) ∧ ((x17 - x18) ≤ (t - 1)) ∧ ((x18 - x78) ≤ (t - 1))))) : (((x18 - x17) ≤ (t - 1)) ∨ ((x18 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8721 (t x17 x18 x78 : ℝ) (h : (((x17 ≤ x18) ∧ (x18 ≤ x78) ∧ ((x78 - x17) ≥ 1) ∧ ((x18 - x17) ≤ (t - 1)) ∧ ((x78 - x18) ≤ (t - 1))) ∨ ((x78 ≤ x18) ∧ (x18 ≤ x17) ∧ ((x17 - x78) ≥ 1) ∧ ((x17 - x18) ≤ (t - 1)) ∧ ((x18 - x78) ≤ (t - 1))))) : (((x78 - x18) ≤ (t - 1)) ∨ (x78 ≤ x18)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x18) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x18) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8722 (t x17 x18 x78 : ℝ) (h : (((x17 ≤ x18) ∧ (x18 ≤ x78) ∧ ((x78 - x17) ≥ 1) ∧ ((x18 - x17) ≤ (t - 1)) ∧ ((x78 - x18) ≤ (t - 1))) ∨ ((x78 ≤ x18) ∧ (x18 ≤ x17) ∧ ((x17 - x78) ≥ 1) ∧ ((x17 - x18) ≤ (t - 1)) ∧ ((x18 - x78) ≤ (t - 1))))) : (((x78 - x18) ≤ (t - 1)) ∨ (x18 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x18) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8723 (t x17 x18 x78 : ℝ) (h : (((x17 ≤ x18) ∧ (x18 ≤ x78) ∧ ((x78 - x17) ≥ 1) ∧ ((x18 - x17) ≤ (t - 1)) ∧ ((x78 - x18) ≤ (t - 1))) ∨ ((x78 ≤ x18) ∧ (x18 ≤ x17) ∧ ((x17 - x78) ≥ 1) ∧ ((x17 - x18) ≤ (t - 1)) ∧ ((x18 - x78) ≤ (t - 1))))) : (((x78 - x18) ≤ (t - 1)) ∨ ((x17 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x18) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8724 (t x17 x18 x78 : ℝ) (h : (((x17 ≤ x18) ∧ (x18 ≤ x78) ∧ ((x78 - x17) ≥ 1) ∧ ((x18 - x17) ≤ (t - 1)) ∧ ((x78 - x18) ≤ (t - 1))) ∨ ((x78 ≤ x18) ∧ (x18 ≤ x17) ∧ ((x17 - x78) ≥ 1) ∧ ((x17 - x18) ≤ (t - 1)) ∧ ((x18 - x78) ≤ (t - 1))))) : (((x78 - x18) ≤ (t - 1)) ∨ ((x17 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x18) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8725 (t x17 x18 x78 : ℝ) (h : (((x17 ≤ x18) ∧ (x18 ≤ x78) ∧ ((x78 - x17) ≥ 1) ∧ ((x18 - x17) ≤ (t - 1)) ∧ ((x78 - x18) ≤ (t - 1))) ∨ ((x78 ≤ x18) ∧ (x18 ≤ x17) ∧ ((x17 - x78) ≥ 1) ∧ ((x17 - x18) ≤ (t - 1)) ∧ ((x18 - x78) ≤ (t - 1))))) : (((x78 - x18) ≤ (t - 1)) ∨ ((x18 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x18) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8726 (x02 x12 x25 : ℝ) : ((¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th594 x02 x12 x25
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 u0)))) h

theorem clause8727 (t x01 x02 x12 x13 x25 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x12 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x02)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th595 t x01 x02 x12 x13 x25
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u2 u4))))))) h

theorem clause8728 (t x02 x14 x24 x25 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((t + ((-1) * x14) + x24) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x25 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x14) + x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th597 t x02 x14 x24 x25 x45
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u1 u5)))))) h

theorem clause8729 (t x04 x05 x24 x34 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x24) + x34) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x24) + x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th599 t x04 x05 x24 x34 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u6 (And.intro u2 u4)))))))) h

theorem clause8731 (x01 x14 x15 : ℝ) : ((¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x15)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th602 x01 x14 x15
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 u0)))) h

theorem clause8732 (t x03 x13 x14 x34 x45 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((t + x03 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x03 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th603 t x03 x13 x14 x34 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u3 (And.intro u1 (And.intro u5 (And.intro u2 u0))))))) h

theorem clause8733 (x14 x34 x45 : ℝ) : ((¬ ((x14 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x14 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th604 x14 x34 x45
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u2 u1))) h

theorem clause8734 (t x03 x13 x34 x35 x45 x56 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ ((t + ((-1) * x13)) ≤ 0) ∨ (¬ ((x35 + ((-1) * x45)) ≥ 0)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1))) := by
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
  have u2 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th605 t x03 x13 x34 x35 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u4 (And.intro u7 (And.intro u6 (And.intro u3 (And.intro u0 u1))))))))) h

theorem clause8735 (t x01 x15 x17 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x15) + x45) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x57)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x15) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th607 t x01 x15 x17 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u5 (And.intro u2 u4))))))) h

theorem clause8736 (x01 x15 x17 : ℝ) : ((¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x17)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x15 + ((-1) * x17)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th608 x01 x15 x17
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 u0))) h

theorem clause8737 (x01 x15 x17 x45 x57 : ℝ) : ((¬ ((x15 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x57)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x15 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x17 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hh))))
  have h := NineTheoryTrial.th609 x01 x15 x17 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u4 (And.intro u1 (And.intro u3 u0)))))) h

theorem clause8738 (x05 x15 x57 : ℝ) : ((¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x15)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x15 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th610 x05 x15 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 u1)))) h

theorem clause8739 (x01 x04 x14 : ℝ) : ((¬ ((x04 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x04)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th611 x01 x04 x14
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 u2)))) h

theorem clause8740 (x02 x12 x24 : ℝ) : ((¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th614 x02 x12 x24
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 u0)))) h

theorem clause8741 (x01 x02 x04 : ℝ) : ((¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0)) ∨ ((x01 + ((-1) * x04)) ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x02)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x01 + ((-1) * x04)) ≥ 0) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th615 x01 x02 x04
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 u2)))) h

theorem clause8742 (x01 x12 x17 : ℝ) : ((¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x17)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x17)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th620 x01 x12 x17
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u2 u0))) h

theorem clause8743 (x05 x25 x57 : ℝ) : ((¬ ((x05 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x05 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th621 x05 x25 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 u1)))) h

theorem clause8744 (t x02 x15 x25 x27 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((t + ((-1) * x15) + x25) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x57)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x15) + x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x15 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th622 t x02 x15 x25 x27 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u4 u3))))))) h

theorem clause8745 (x14 x24 x45 : ℝ) : ((¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th624 x14 x24 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause8746 (t x01 x04 x12 x23 x35 x46 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x04)) ≥ 1)) ∨ ((t + ((-1) * x35)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x01 + ((-1) * x04)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th626 t x01 x04 x12 x23 x35 x46 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u7 (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u9 (And.intro u8 (And.intro u5 (And.intro u6 u4))))))))))) h

theorem clause8747 (t x01 x02 x12 x27 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hh))))
  have h := NineTheoryTrial.th627 t x01 x02 x12 x27
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u1 u3)))))) h

theorem clause8748 (t x01 x02 x12 x13 x24 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x12) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x02)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th631 t x01 x02 x12 x13 x24
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u4 u2))))))) h

theorem clause8749 (t x01 x12 x13 x23 x24 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((t + x23 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1)))) := by
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
  have u4 : ((t + x23 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th632 t x01 x12 x13 x23 x24
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u4 u3))))))) h

theorem clause8750 (t x01 x02 x12 x23 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hh))))
  have h := NineTheoryTrial.th633 t x01 x02 x12 x23
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u3 (And.intro u0 u4)))))) h

theorem clause8751 (t x02 x03 x23 x26 x27 x34 x45 x57 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((t + x23 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + x27 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x23 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x27 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x02 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th634 t x02 x03 x23 x26 x27 x34 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u7 (And.intro u6 (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u8 (And.intro u4 u5)))))))))) h

theorem clause8752 (t x01 x13 x15 x34 x35 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + x34 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x34 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th637 t x01 x13 x15 x34 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u5 u2))))))) h

theorem clause8753 (x01 x13 x15 : ℝ) : ((¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x15)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th638 x01 x13 x15
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u2 u0))) h

theorem clause8754 (t x01 x12 x13 x34 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ (x45 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th639 t x01 x12 x13 x34 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u6 (And.intro u4 (And.intro u5 (And.intro u2 u1)))))))) h

theorem clause8755 (x01 x03 x13 x15 : ℝ) : ((¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x15)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th640 x01 x03 x13 x15
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u0 u3))))) h

theorem clause8756 (x02 x03 x04 : ℝ) : (((x02 + ((-1) * x03)) ≥ 0) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x03)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th643 x02 x03 x04
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 u0)))) h

theorem clause8758 (x02 x24 x25 : ℝ) : ((¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x25)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th646 x02 x24 x25
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 u0)))) h

theorem clause8759 (x01 x12 x15 : ℝ) : ((¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x15)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th648 x01 x12 x15
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 u0)))) h

theorem clause8760 (t x01 x02 x12 x13 x25 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x12) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x02)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th649 t x01 x02 x12 x13 x25
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u0 u2))))))) h

theorem clause8761 (t x01 x14 x17 x24 x34 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((t + x24 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x47)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x24 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x17 + ((-1) * x47)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th651 t x01 x14 x17 x24 x34 x47
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 (And.intro u0 (And.intro u6 (And.intro u4 (And.intro u3 u5))))))) h

theorem clause8762 (x34 x47 : ℝ) : ((¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th655 x34 x47
  exact (fun hh => (Or.elim hh (fun hh => hh u1) (fun zz => ((fun hh => hh u0) zz)))) h

theorem clause8763 (x34 x45 x47 : ℝ) : ((¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x47)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th657 x34 x45 x47
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u2 u1))) h

theorem clause8765 (x14 x34 x37 x47 : ℝ) : ((¬ ((x14 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x37)) ≤ 0)) ∨ (¬ ((x37 + ((-1) * x47)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x14 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x37)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x37 + ((-1) * x47)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th662 x14 x34 x37 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u1 u0))))) h

theorem clause8767 (x01 x15 : ℝ) : ((¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th665 x01 x15
  exact (fun hh => (Or.elim hh (fun hh => hh u1) (fun zz => ((fun hh => hh u0) zz)))) h

theorem clause8768 (x14 x47 : ℝ) : ((¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x14 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th666 x14 x47
  exact (fun hh => (Or.elim hh (fun hh => hh u1) (fun zz => ((fun hh => hh u0) zz)))) h

theorem clause8769 (t x01 x13 x15 x35 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ ((t + ((-1) * x35)) ≤ 0) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th669 t x01 x13 x15 x35 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u6 u5)))))))) h

theorem clause8770 (t x01 x13 x14 x34 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ ((t + ((-1) * x57)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th671 t x01 x13 x14 x34 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u7 (And.intro u6 u5))))))))) h

theorem clause8771 (t x34 x45 x47 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x57)) ≤ 0)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x56 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th672 t x34 x45 x47 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u5 u4))))))) h

theorem clause8772 (t x05 x34 x35 x45 x47 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((t + x45 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x45 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th673 t x05 x34 x35 x45 x47 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u6 (And.intro u4 (And.intro u5 u1)))))))) h

theorem clause8773 (x34 x35 x47 x57 : ℝ) : ((¬ ((x34 + ((-1) * x35)) ≥ 0)) ∨ ((x35 + ((-1) * x57)) ≤ (-1)) ∨ (¬ ((x47 + ((-1) * x57)) ≤ 0)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x47 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th674 x34 x35 x47 x57
  exact (fun hh => u1 (hh (And.intro u2 (And.intro u3 u0)))) h

theorem clause8774 (t x01 x13 x15 x35 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x15 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th675 t x01 x13 x15 x35 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u4 (And.intro u2 (And.intro u6 (And.intro u5 (And.intro u1 u7))))))))) h

theorem clause8776 (t x01 x15 x35 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ ((t + ((-1) * x57)) ≤ 0) ∨ (¬ (x01 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th677 t x01 x15 x35 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u3 (And.intro u4 (And.intro u1 (And.intro u0 (And.intro u2 u5)))))))) h

theorem clause8777 (t x01 x12 x15 x16 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x15 + ((-1) * x16)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th678 t x01 x12 x15 x16 x56 x67
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u0 (And.intro u7 (And.intro u1 (And.intro u2 (And.intro u3 (And.intro u6 u4)))))))) h

theorem clause8778 (x16 x56 x67 : ℝ) : ((¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x16 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th679 x16 x56 x67
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u2 u0))) h

theorem clause8779 (t x01 x13 x15 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th681 t x01 x13 x15 x57 x78
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u3 (And.intro u0 (And.intro u6 (And.intro u5 (And.intro u2 u1))))))) h

theorem clause8780 (x01 x13 x17 : ℝ) : ((¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x17)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x17)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th682 x01 x13 x17
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 u0)))) h

theorem clause8782 (t x03 x34 x47 x57 x78 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ (x03 ≥ 0)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ ((t + ((-1) * x57)) ≤ 0) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th687 t x03 x34 x47 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u5 (And.intro u1 (And.intro u4 (And.intro u6 u0)))))))) h

theorem clause8785 (t x47 x48 x78 : ℝ) : (((x47 + ((-1) * x48)) ≤ 0) ∨ ((x47 + ((-1) * x78)) ≥ 1) ∨ (¬ (x47 ≤ x48)) ∨ (¬ (x48 ≤ x78)) ∨ (¬ ((x78 - x47) ≥ 1)) ∨ (¬ ((x48 - x47) ≤ (t - 1))) ∨ (¬ ((x78 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 + ((-1) * x48)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x48 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th689 t x47 x48 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8794 (t x47 x48 x78 : ℝ) : (((x47 + ((-1) * x78)) ≤ (-1)) ∨ ((x47 + ((-1) * x48)) ≥ 0) ∨ (¬ (x47 ≤ x48)) ∨ (¬ (x48 ≤ x78)) ∨ (¬ ((x78 - x47) ≥ 1)) ∨ (¬ ((x48 - x47) ≤ (t - 1))) ∨ (¬ ((x78 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 + ((-1) * x48)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x48 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th689 t x47 x48 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8795 (t x47 x48 x78 : ℝ) : (((x47 + ((-1) * x78)) ≤ (-1)) ∨ ((x47 + ((-1) * x78)) ≥ 1) ∨ (¬ (x47 ≤ x48)) ∨ (¬ (x48 ≤ x78)) ∨ (¬ ((x78 - x47) ≥ 1)) ∨ (¬ ((x48 - x47) ≤ (t - 1))) ∨ (¬ ((x78 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x48 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th689 t x47 x48 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8797 (t x47 x48 x78 : ℝ) : (((x47 + ((-1) * x78)) ≤ (-1)) ∨ ((t + ((-1) * x48) + x78) ≥ 1) ∨ (¬ (x47 ≤ x48)) ∨ (¬ (x48 ≤ x78)) ∨ (¬ ((x78 - x47) ≥ 1)) ∨ (¬ ((x48 - x47) ≤ (t - 1))) ∨ (¬ ((x78 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x48) + x78) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x48 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th689 t x47 x48 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8805 (t x47 x48 x78 : ℝ) : (((t + x48 + ((-1) * x78)) ≥ 1) ∨ ((x47 + ((-1) * x78)) ≥ 1) ∨ (¬ (x47 ≤ x48)) ∨ (¬ (x48 ≤ x78)) ∨ (¬ ((x78 - x47) ≥ 1)) ∨ (¬ ((x48 - x47) ≤ (t - 1))) ∨ (¬ ((x78 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x48 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x48 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th689 t x47 x48 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8810 (t x47 x48 x78 : ℝ) : (((x47 + ((-1) * x48)) ≤ 0) ∨ ((x47 + ((-1) * x78)) ≥ 1) ∨ (¬ (x78 ≤ x48)) ∨ (¬ (x48 ≤ x47)) ∨ (¬ ((x47 - x78) ≥ 1)) ∨ (¬ ((x47 - x48) ≤ (t - 1))) ∨ (¬ ((x48 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 + ((-1) * x48)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th689 t x47 x48 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8819 (t x47 x48 x78 : ℝ) : (((x47 + ((-1) * x78)) ≤ (-1)) ∨ ((x47 + ((-1) * x48)) ≥ 0) ∨ (¬ (x78 ≤ x48)) ∨ (¬ (x48 ≤ x47)) ∨ (¬ ((x47 - x78) ≥ 1)) ∨ (¬ ((x47 - x48) ≤ (t - 1))) ∨ (¬ ((x48 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 + ((-1) * x48)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th689 t x47 x48 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8820 (t x47 x48 x78 : ℝ) : (((x47 + ((-1) * x78)) ≤ (-1)) ∨ ((x47 + ((-1) * x78)) ≥ 1) ∨ (¬ (x78 ≤ x48)) ∨ (¬ (x48 ≤ x47)) ∨ (¬ ((x47 - x78) ≥ 1)) ∨ (¬ ((x47 - x48) ≤ (t - 1))) ∨ (¬ ((x48 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th689 t x47 x48 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8822 (t x47 x48 x78 : ℝ) : (((x47 + ((-1) * x78)) ≤ (-1)) ∨ ((t + ((-1) * x48) + x78) ≥ 1) ∨ (¬ (x78 ≤ x48)) ∨ (¬ (x48 ≤ x47)) ∨ (¬ ((x47 - x78) ≥ 1)) ∨ (¬ ((x47 - x48) ≤ (t - 1))) ∨ (¬ ((x48 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x48) + x78) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th689 t x47 x48 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8830 (t x47 x48 x78 : ℝ) : (((t + x48 + ((-1) * x78)) ≥ 1) ∨ ((x47 + ((-1) * x78)) ≥ 1) ∨ (¬ (x78 ≤ x48)) ∨ (¬ (x48 ≤ x47)) ∨ (¬ ((x47 - x78) ≥ 1)) ∨ (¬ ((x47 - x48) ≤ (t - 1))) ∨ (¬ ((x48 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x48 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th689 t x47 x48 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8883 (t x47 x48 x78 : ℝ) (h : (((x47 ≤ x48) ∧ (x48 ≤ x78) ∧ ((x78 - x47) ≥ 1) ∧ ((x48 - x47) ≤ (t - 1)) ∧ ((x78 - x48) ≤ (t - 1))) ∨ ((x78 ≤ x48) ∧ (x48 ≤ x47) ∧ ((x47 - x78) ≥ 1) ∧ ((x47 - x48) ≤ (t - 1)) ∧ ((x48 - x78) ≤ (t - 1))))) : ((x47 ≤ x48) ∨ (x78 ≤ x48)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x47 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x48) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8884 (t x47 x48 x78 : ℝ) (h : (((x47 ≤ x48) ∧ (x48 ≤ x78) ∧ ((x78 - x47) ≥ 1) ∧ ((x48 - x47) ≤ (t - 1)) ∧ ((x78 - x48) ≤ (t - 1))) ∨ ((x78 ≤ x48) ∧ (x48 ≤ x47) ∧ ((x47 - x78) ≥ 1) ∧ ((x47 - x48) ≤ (t - 1)) ∧ ((x48 - x78) ≤ (t - 1))))) : ((x47 ≤ x48) ∨ (x48 ≤ x47)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x47 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x47) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8885 (t x47 x48 x78 : ℝ) (h : (((x47 ≤ x48) ∧ (x48 ≤ x78) ∧ ((x78 - x47) ≥ 1) ∧ ((x48 - x47) ≤ (t - 1)) ∧ ((x78 - x48) ≤ (t - 1))) ∨ ((x78 ≤ x48) ∧ (x48 ≤ x47) ∧ ((x47 - x78) ≥ 1) ∧ ((x47 - x48) ≤ (t - 1)) ∧ ((x48 - x78) ≤ (t - 1))))) : ((x47 ≤ x48) ∨ ((x47 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x47 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8886 (t x47 x48 x78 : ℝ) (h : (((x47 ≤ x48) ∧ (x48 ≤ x78) ∧ ((x78 - x47) ≥ 1) ∧ ((x48 - x47) ≤ (t - 1)) ∧ ((x78 - x48) ≤ (t - 1))) ∨ ((x78 ≤ x48) ∧ (x48 ≤ x47) ∧ ((x47 - x78) ≥ 1) ∧ ((x47 - x48) ≤ (t - 1)) ∧ ((x48 - x78) ≤ (t - 1))))) : ((x47 ≤ x48) ∨ ((x47 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x47 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8887 (t x47 x48 x78 : ℝ) (h : (((x47 ≤ x48) ∧ (x48 ≤ x78) ∧ ((x78 - x47) ≥ 1) ∧ ((x48 - x47) ≤ (t - 1)) ∧ ((x78 - x48) ≤ (t - 1))) ∨ ((x78 ≤ x48) ∧ (x48 ≤ x47) ∧ ((x47 - x78) ≥ 1) ∧ ((x47 - x48) ≤ (t - 1)) ∧ ((x48 - x78) ≤ (t - 1))))) : ((x47 ≤ x48) ∨ ((x48 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x47 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x48 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8888 (t x47 x48 x78 : ℝ) (h : (((x47 ≤ x48) ∧ (x48 ≤ x78) ∧ ((x78 - x47) ≥ 1) ∧ ((x48 - x47) ≤ (t - 1)) ∧ ((x78 - x48) ≤ (t - 1))) ∨ ((x78 ≤ x48) ∧ (x48 ≤ x47) ∧ ((x47 - x78) ≥ 1) ∧ ((x47 - x48) ≤ (t - 1)) ∧ ((x48 - x78) ≤ (t - 1))))) : ((x48 ≤ x78) ∨ (x78 ≤ x48)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x48 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x48) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8889 (t x47 x48 x78 : ℝ) (h : (((x47 ≤ x48) ∧ (x48 ≤ x78) ∧ ((x78 - x47) ≥ 1) ∧ ((x48 - x47) ≤ (t - 1)) ∧ ((x78 - x48) ≤ (t - 1))) ∨ ((x78 ≤ x48) ∧ (x48 ≤ x47) ∧ ((x47 - x78) ≥ 1) ∧ ((x47 - x48) ≤ (t - 1)) ∧ ((x48 - x78) ≤ (t - 1))))) : ((x48 ≤ x78) ∨ (x48 ≤ x47)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x48 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x47) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8890 (t x47 x48 x78 : ℝ) (h : (((x47 ≤ x48) ∧ (x48 ≤ x78) ∧ ((x78 - x47) ≥ 1) ∧ ((x48 - x47) ≤ (t - 1)) ∧ ((x78 - x48) ≤ (t - 1))) ∨ ((x78 ≤ x48) ∧ (x48 ≤ x47) ∧ ((x47 - x78) ≥ 1) ∧ ((x47 - x48) ≤ (t - 1)) ∧ ((x48 - x78) ≤ (t - 1))))) : ((x48 ≤ x78) ∨ ((x47 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x48 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8891 (t x47 x48 x78 : ℝ) (h : (((x47 ≤ x48) ∧ (x48 ≤ x78) ∧ ((x78 - x47) ≥ 1) ∧ ((x48 - x47) ≤ (t - 1)) ∧ ((x78 - x48) ≤ (t - 1))) ∨ ((x78 ≤ x48) ∧ (x48 ≤ x47) ∧ ((x47 - x78) ≥ 1) ∧ ((x47 - x48) ≤ (t - 1)) ∧ ((x48 - x78) ≤ (t - 1))))) : ((x48 ≤ x78) ∨ ((x47 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x48 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8892 (t x47 x48 x78 : ℝ) (h : (((x47 ≤ x48) ∧ (x48 ≤ x78) ∧ ((x78 - x47) ≥ 1) ∧ ((x48 - x47) ≤ (t - 1)) ∧ ((x78 - x48) ≤ (t - 1))) ∨ ((x78 ≤ x48) ∧ (x48 ≤ x47) ∧ ((x47 - x78) ≥ 1) ∧ ((x47 - x48) ≤ (t - 1)) ∧ ((x48 - x78) ≤ (t - 1))))) : ((x48 ≤ x78) ∨ ((x48 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x48 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x48 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8893 (t x47 x48 x78 : ℝ) (h : (((x47 ≤ x48) ∧ (x48 ≤ x78) ∧ ((x78 - x47) ≥ 1) ∧ ((x48 - x47) ≤ (t - 1)) ∧ ((x78 - x48) ≤ (t - 1))) ∨ ((x78 ≤ x48) ∧ (x48 ≤ x47) ∧ ((x47 - x78) ≥ 1) ∧ ((x47 - x48) ≤ (t - 1)) ∧ ((x48 - x78) ≤ (t - 1))))) : (((x78 - x47) ≥ 1) ∨ (x78 ≤ x48)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x47) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x48) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8894 (t x47 x48 x78 : ℝ) (h : (((x47 ≤ x48) ∧ (x48 ≤ x78) ∧ ((x78 - x47) ≥ 1) ∧ ((x48 - x47) ≤ (t - 1)) ∧ ((x78 - x48) ≤ (t - 1))) ∨ ((x78 ≤ x48) ∧ (x48 ≤ x47) ∧ ((x47 - x78) ≥ 1) ∧ ((x47 - x48) ≤ (t - 1)) ∧ ((x48 - x78) ≤ (t - 1))))) : (((x78 - x47) ≥ 1) ∨ (x48 ≤ x47)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x47) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x47) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8895 (t x47 x48 x78 : ℝ) (h : (((x47 ≤ x48) ∧ (x48 ≤ x78) ∧ ((x78 - x47) ≥ 1) ∧ ((x48 - x47) ≤ (t - 1)) ∧ ((x78 - x48) ≤ (t - 1))) ∨ ((x78 ≤ x48) ∧ (x48 ≤ x47) ∧ ((x47 - x78) ≥ 1) ∧ ((x47 - x48) ≤ (t - 1)) ∧ ((x48 - x78) ≤ (t - 1))))) : (((x78 - x47) ≥ 1) ∨ ((x47 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x47) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8896 (t x47 x48 x78 : ℝ) (h : (((x47 ≤ x48) ∧ (x48 ≤ x78) ∧ ((x78 - x47) ≥ 1) ∧ ((x48 - x47) ≤ (t - 1)) ∧ ((x78 - x48) ≤ (t - 1))) ∨ ((x78 ≤ x48) ∧ (x48 ≤ x47) ∧ ((x47 - x78) ≥ 1) ∧ ((x47 - x48) ≤ (t - 1)) ∧ ((x48 - x78) ≤ (t - 1))))) : (((x78 - x47) ≥ 1) ∨ ((x47 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x47) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8897 (t x47 x48 x78 : ℝ) (h : (((x47 ≤ x48) ∧ (x48 ≤ x78) ∧ ((x78 - x47) ≥ 1) ∧ ((x48 - x47) ≤ (t - 1)) ∧ ((x78 - x48) ≤ (t - 1))) ∨ ((x78 ≤ x48) ∧ (x48 ≤ x47) ∧ ((x47 - x78) ≥ 1) ∧ ((x47 - x48) ≤ (t - 1)) ∧ ((x48 - x78) ≤ (t - 1))))) : (((x78 - x47) ≥ 1) ∨ ((x48 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x47) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x48 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8898 (t x47 x48 x78 : ℝ) (h : (((x47 ≤ x48) ∧ (x48 ≤ x78) ∧ ((x78 - x47) ≥ 1) ∧ ((x48 - x47) ≤ (t - 1)) ∧ ((x78 - x48) ≤ (t - 1))) ∨ ((x78 ≤ x48) ∧ (x48 ≤ x47) ∧ ((x47 - x78) ≥ 1) ∧ ((x47 - x48) ≤ (t - 1)) ∧ ((x48 - x78) ≤ (t - 1))))) : (((x48 - x47) ≤ (t - 1)) ∨ (x78 ≤ x48)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x47) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x48) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8899 (t x47 x48 x78 : ℝ) (h : (((x47 ≤ x48) ∧ (x48 ≤ x78) ∧ ((x78 - x47) ≥ 1) ∧ ((x48 - x47) ≤ (t - 1)) ∧ ((x78 - x48) ≤ (t - 1))) ∨ ((x78 ≤ x48) ∧ (x48 ≤ x47) ∧ ((x47 - x78) ≥ 1) ∧ ((x47 - x48) ≤ (t - 1)) ∧ ((x48 - x78) ≤ (t - 1))))) : (((x48 - x47) ≤ (t - 1)) ∨ (x48 ≤ x47)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x47) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x47) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8900 (t x47 x48 x78 : ℝ) (h : (((x47 ≤ x48) ∧ (x48 ≤ x78) ∧ ((x78 - x47) ≥ 1) ∧ ((x48 - x47) ≤ (t - 1)) ∧ ((x78 - x48) ≤ (t - 1))) ∨ ((x78 ≤ x48) ∧ (x48 ≤ x47) ∧ ((x47 - x78) ≥ 1) ∧ ((x47 - x48) ≤ (t - 1)) ∧ ((x48 - x78) ≤ (t - 1))))) : (((x48 - x47) ≤ (t - 1)) ∨ ((x47 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x47) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8901 (t x47 x48 x78 : ℝ) (h : (((x47 ≤ x48) ∧ (x48 ≤ x78) ∧ ((x78 - x47) ≥ 1) ∧ ((x48 - x47) ≤ (t - 1)) ∧ ((x78 - x48) ≤ (t - 1))) ∨ ((x78 ≤ x48) ∧ (x48 ≤ x47) ∧ ((x47 - x78) ≥ 1) ∧ ((x47 - x48) ≤ (t - 1)) ∧ ((x48 - x78) ≤ (t - 1))))) : (((x48 - x47) ≤ (t - 1)) ∨ ((x47 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x47) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8902 (t x47 x48 x78 : ℝ) (h : (((x47 ≤ x48) ∧ (x48 ≤ x78) ∧ ((x78 - x47) ≥ 1) ∧ ((x48 - x47) ≤ (t - 1)) ∧ ((x78 - x48) ≤ (t - 1))) ∨ ((x78 ≤ x48) ∧ (x48 ≤ x47) ∧ ((x47 - x78) ≥ 1) ∧ ((x47 - x48) ≤ (t - 1)) ∧ ((x48 - x78) ≤ (t - 1))))) : (((x48 - x47) ≤ (t - 1)) ∨ ((x48 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x47) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x48 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8903 (t x47 x48 x78 : ℝ) (h : (((x47 ≤ x48) ∧ (x48 ≤ x78) ∧ ((x78 - x47) ≥ 1) ∧ ((x48 - x47) ≤ (t - 1)) ∧ ((x78 - x48) ≤ (t - 1))) ∨ ((x78 ≤ x48) ∧ (x48 ≤ x47) ∧ ((x47 - x78) ≥ 1) ∧ ((x47 - x48) ≤ (t - 1)) ∧ ((x48 - x78) ≤ (t - 1))))) : (((x78 - x48) ≤ (t - 1)) ∨ (x78 ≤ x48)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x48) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x48) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8904 (t x47 x48 x78 : ℝ) (h : (((x47 ≤ x48) ∧ (x48 ≤ x78) ∧ ((x78 - x47) ≥ 1) ∧ ((x48 - x47) ≤ (t - 1)) ∧ ((x78 - x48) ≤ (t - 1))) ∨ ((x78 ≤ x48) ∧ (x48 ≤ x47) ∧ ((x47 - x78) ≥ 1) ∧ ((x47 - x48) ≤ (t - 1)) ∧ ((x48 - x78) ≤ (t - 1))))) : (((x78 - x48) ≤ (t - 1)) ∨ (x48 ≤ x47)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x48) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x47) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8905 (t x47 x48 x78 : ℝ) (h : (((x47 ≤ x48) ∧ (x48 ≤ x78) ∧ ((x78 - x47) ≥ 1) ∧ ((x48 - x47) ≤ (t - 1)) ∧ ((x78 - x48) ≤ (t - 1))) ∨ ((x78 ≤ x48) ∧ (x48 ≤ x47) ∧ ((x47 - x78) ≥ 1) ∧ ((x47 - x48) ≤ (t - 1)) ∧ ((x48 - x78) ≤ (t - 1))))) : (((x78 - x48) ≤ (t - 1)) ∨ ((x47 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x48) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8906 (t x47 x48 x78 : ℝ) (h : (((x47 ≤ x48) ∧ (x48 ≤ x78) ∧ ((x78 - x47) ≥ 1) ∧ ((x48 - x47) ≤ (t - 1)) ∧ ((x78 - x48) ≤ (t - 1))) ∨ ((x78 ≤ x48) ∧ (x48 ≤ x47) ∧ ((x47 - x78) ≥ 1) ∧ ((x47 - x48) ≤ (t - 1)) ∧ ((x48 - x78) ≤ (t - 1))))) : (((x78 - x48) ≤ (t - 1)) ∨ ((x47 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x48) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8907 (t x47 x48 x78 : ℝ) (h : (((x47 ≤ x48) ∧ (x48 ≤ x78) ∧ ((x78 - x47) ≥ 1) ∧ ((x48 - x47) ≤ (t - 1)) ∧ ((x78 - x48) ≤ (t - 1))) ∨ ((x78 ≤ x48) ∧ (x48 ≤ x47) ∧ ((x47 - x78) ≥ 1) ∧ ((x47 - x48) ≤ (t - 1)) ∧ ((x48 - x78) ≤ (t - 1))))) : (((x78 - x48) ≤ (t - 1)) ∨ ((x48 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x48) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x48 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8908 (t x34 x37 x45 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x45 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x37)) ≤ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x45 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x37)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th691 t x34 x37 x45 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u3 (And.intro u1 (And.intro u5 (And.intro u2 u0))))))) h

theorem clause8919 (t x37 x38 x78 : ℝ) : (((x37 + ((-1) * x78)) ≤ (-1)) ∨ ((x38 + ((-1) * x78)) ≥ 0) ∨ (¬ (x37 ≤ x38)) ∨ (¬ (x38 ≤ x78)) ∨ (¬ ((x78 - x37) ≥ 1)) ∨ (¬ ((x38 - x37) ≤ (t - 1))) ∨ (¬ ((x78 - x38) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 + ((-1) * x78)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x38 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th694 t x37 x38 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8920 (t x37 x38 x78 : ℝ) : (((x37 + ((-1) * x78)) ≤ (-1)) ∨ ((x37 + ((-1) * x38)) ≥ 0) ∨ (¬ (x37 ≤ x38)) ∨ (¬ (x38 ≤ x78)) ∨ (¬ ((x78 - x37) ≥ 1)) ∨ (¬ ((x38 - x37) ≤ (t - 1))) ∨ (¬ ((x78 - x38) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 + ((-1) * x38)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x38 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th694 t x37 x38 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8921 (t x37 x38 x78 : ℝ) : (((x37 + ((-1) * x78)) ≥ 1) ∨ ((x37 + ((-1) * x78)) ≤ (-1)) ∨ (¬ (x37 ≤ x38)) ∨ (¬ (x38 ≤ x78)) ∨ (¬ ((x78 - x37) ≥ 1)) ∨ (¬ ((x38 - x37) ≤ (t - 1))) ∨ (¬ ((x78 - x38) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x38 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th694 t x37 x38 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8923 (t x37 x38 x78 : ℝ) : (((x37 + ((-1) * x78)) ≤ (-1)) ∨ ((t + ((-1) * x38) + x78) ≥ 1) ∨ (¬ (x37 ≤ x38)) ∨ (¬ (x38 ≤ x78)) ∨ (¬ ((x78 - x37) ≥ 1)) ∨ (¬ ((x38 - x37) ≤ (t - 1))) ∨ (¬ ((x78 - x38) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x38) + x78) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x38 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th694 t x37 x38 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8931 (t x37 x38 x78 : ℝ) : (((x37 + ((-1) * x78)) ≥ 1) ∨ ((t + x38 + ((-1) * x78)) ≥ 1) ∨ (¬ (x37 ≤ x38)) ∨ (¬ (x38 ≤ x78)) ∨ (¬ ((x78 - x37) ≥ 1)) ∨ (¬ ((x38 - x37) ≤ (t - 1))) ∨ (¬ ((x78 - x38) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x38 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x38 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th694 t x37 x38 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8944 (t x37 x38 x78 : ℝ) : (((x37 + ((-1) * x78)) ≤ (-1)) ∨ ((x38 + ((-1) * x78)) ≥ 0) ∨ (¬ (x78 ≤ x38)) ∨ (¬ (x38 ≤ x37)) ∨ (¬ ((x37 - x78) ≥ 1)) ∨ (¬ ((x37 - x38) ≤ (t - 1))) ∨ (¬ ((x38 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 + ((-1) * x78)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x38 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th694 t x37 x38 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8945 (t x37 x38 x78 : ℝ) : (((x37 + ((-1) * x78)) ≤ (-1)) ∨ ((x37 + ((-1) * x38)) ≥ 0) ∨ (¬ (x78 ≤ x38)) ∨ (¬ (x38 ≤ x37)) ∨ (¬ ((x37 - x78) ≥ 1)) ∨ (¬ ((x37 - x38) ≤ (t - 1))) ∨ (¬ ((x38 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 + ((-1) * x38)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x38 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th694 t x37 x38 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8946 (t x37 x38 x78 : ℝ) : (((x37 + ((-1) * x78)) ≥ 1) ∨ ((x37 + ((-1) * x78)) ≤ (-1)) ∨ (¬ (x78 ≤ x38)) ∨ (¬ (x38 ≤ x37)) ∨ (¬ ((x37 - x78) ≥ 1)) ∨ (¬ ((x37 - x38) ≤ (t - 1))) ∨ (¬ ((x38 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x38 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th694 t x37 x38 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8948 (t x37 x38 x78 : ℝ) : (((x37 + ((-1) * x78)) ≤ (-1)) ∨ ((t + ((-1) * x38) + x78) ≥ 1) ∨ (¬ (x78 ≤ x38)) ∨ (¬ (x38 ≤ x37)) ∨ (¬ ((x37 - x78) ≥ 1)) ∨ (¬ ((x37 - x38) ≤ (t - 1))) ∨ (¬ ((x38 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x38) + x78) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x38 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th694 t x37 x38 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8956 (t x37 x38 x78 : ℝ) : (((x37 + ((-1) * x78)) ≥ 1) ∨ ((t + x38 + ((-1) * x78)) ≥ 1) ∨ (¬ (x78 ≤ x38)) ∨ (¬ (x38 ≤ x37)) ∨ (¬ ((x37 - x78) ≥ 1)) ∨ (¬ ((x37 - x38) ≤ (t - 1))) ∨ (¬ ((x38 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x38 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x38 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th694 t x37 x38 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9009 (t x37 x38 x78 : ℝ) (h : (((x37 ≤ x38) ∧ (x38 ≤ x78) ∧ ((x78 - x37) ≥ 1) ∧ ((x38 - x37) ≤ (t - 1)) ∧ ((x78 - x38) ≤ (t - 1))) ∨ ((x78 ≤ x38) ∧ (x38 ≤ x37) ∧ ((x37 - x78) ≥ 1) ∧ ((x37 - x38) ≤ (t - 1)) ∧ ((x38 - x78) ≤ (t - 1))))) : ((x37 ≤ x38) ∨ (x78 ≤ x38)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x37 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x38) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9010 (t x37 x38 x78 : ℝ) (h : (((x37 ≤ x38) ∧ (x38 ≤ x78) ∧ ((x78 - x37) ≥ 1) ∧ ((x38 - x37) ≤ (t - 1)) ∧ ((x78 - x38) ≤ (t - 1))) ∨ ((x78 ≤ x38) ∧ (x38 ≤ x37) ∧ ((x37 - x78) ≥ 1) ∧ ((x37 - x38) ≤ (t - 1)) ∧ ((x38 - x78) ≤ (t - 1))))) : ((x37 ≤ x38) ∨ (x38 ≤ x37)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x37 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x37) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9011 (t x37 x38 x78 : ℝ) (h : (((x37 ≤ x38) ∧ (x38 ≤ x78) ∧ ((x78 - x37) ≥ 1) ∧ ((x38 - x37) ≤ (t - 1)) ∧ ((x78 - x38) ≤ (t - 1))) ∨ ((x78 ≤ x38) ∧ (x38 ≤ x37) ∧ ((x37 - x78) ≥ 1) ∧ ((x37 - x38) ≤ (t - 1)) ∧ ((x38 - x78) ≤ (t - 1))))) : ((x37 ≤ x38) ∨ ((x37 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x37 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9012 (t x37 x38 x78 : ℝ) (h : (((x37 ≤ x38) ∧ (x38 ≤ x78) ∧ ((x78 - x37) ≥ 1) ∧ ((x38 - x37) ≤ (t - 1)) ∧ ((x78 - x38) ≤ (t - 1))) ∨ ((x78 ≤ x38) ∧ (x38 ≤ x37) ∧ ((x37 - x78) ≥ 1) ∧ ((x37 - x38) ≤ (t - 1)) ∧ ((x38 - x78) ≤ (t - 1))))) : ((x37 ≤ x38) ∨ ((x37 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x37 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9013 (t x37 x38 x78 : ℝ) (h : (((x37 ≤ x38) ∧ (x38 ≤ x78) ∧ ((x78 - x37) ≥ 1) ∧ ((x38 - x37) ≤ (t - 1)) ∧ ((x78 - x38) ≤ (t - 1))) ∨ ((x78 ≤ x38) ∧ (x38 ≤ x37) ∧ ((x37 - x78) ≥ 1) ∧ ((x37 - x38) ≤ (t - 1)) ∧ ((x38 - x78) ≤ (t - 1))))) : ((x37 ≤ x38) ∨ ((x38 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x37 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9014 (t x37 x38 x78 : ℝ) (h : (((x37 ≤ x38) ∧ (x38 ≤ x78) ∧ ((x78 - x37) ≥ 1) ∧ ((x38 - x37) ≤ (t - 1)) ∧ ((x78 - x38) ≤ (t - 1))) ∨ ((x78 ≤ x38) ∧ (x38 ≤ x37) ∧ ((x37 - x78) ≥ 1) ∧ ((x37 - x38) ≤ (t - 1)) ∧ ((x38 - x78) ≤ (t - 1))))) : ((x38 ≤ x78) ∨ (x78 ≤ x38)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x38 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x38) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9015 (t x37 x38 x78 : ℝ) (h : (((x37 ≤ x38) ∧ (x38 ≤ x78) ∧ ((x78 - x37) ≥ 1) ∧ ((x38 - x37) ≤ (t - 1)) ∧ ((x78 - x38) ≤ (t - 1))) ∨ ((x78 ≤ x38) ∧ (x38 ≤ x37) ∧ ((x37 - x78) ≥ 1) ∧ ((x37 - x38) ≤ (t - 1)) ∧ ((x38 - x78) ≤ (t - 1))))) : ((x38 ≤ x78) ∨ (x38 ≤ x37)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x38 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x37) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9016 (t x37 x38 x78 : ℝ) (h : (((x37 ≤ x38) ∧ (x38 ≤ x78) ∧ ((x78 - x37) ≥ 1) ∧ ((x38 - x37) ≤ (t - 1)) ∧ ((x78 - x38) ≤ (t - 1))) ∨ ((x78 ≤ x38) ∧ (x38 ≤ x37) ∧ ((x37 - x78) ≥ 1) ∧ ((x37 - x38) ≤ (t - 1)) ∧ ((x38 - x78) ≤ (t - 1))))) : ((x38 ≤ x78) ∨ ((x37 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x38 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9017 (t x37 x38 x78 : ℝ) (h : (((x37 ≤ x38) ∧ (x38 ≤ x78) ∧ ((x78 - x37) ≥ 1) ∧ ((x38 - x37) ≤ (t - 1)) ∧ ((x78 - x38) ≤ (t - 1))) ∨ ((x78 ≤ x38) ∧ (x38 ≤ x37) ∧ ((x37 - x78) ≥ 1) ∧ ((x37 - x38) ≤ (t - 1)) ∧ ((x38 - x78) ≤ (t - 1))))) : ((x38 ≤ x78) ∨ ((x37 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x38 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9018 (t x37 x38 x78 : ℝ) (h : (((x37 ≤ x38) ∧ (x38 ≤ x78) ∧ ((x78 - x37) ≥ 1) ∧ ((x38 - x37) ≤ (t - 1)) ∧ ((x78 - x38) ≤ (t - 1))) ∨ ((x78 ≤ x38) ∧ (x38 ≤ x37) ∧ ((x37 - x78) ≥ 1) ∧ ((x37 - x38) ≤ (t - 1)) ∧ ((x38 - x78) ≤ (t - 1))))) : ((x38 ≤ x78) ∨ ((x38 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x38 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9019 (t x37 x38 x78 : ℝ) (h : (((x37 ≤ x38) ∧ (x38 ≤ x78) ∧ ((x78 - x37) ≥ 1) ∧ ((x38 - x37) ≤ (t - 1)) ∧ ((x78 - x38) ≤ (t - 1))) ∨ ((x78 ≤ x38) ∧ (x38 ≤ x37) ∧ ((x37 - x78) ≥ 1) ∧ ((x37 - x38) ≤ (t - 1)) ∧ ((x38 - x78) ≤ (t - 1))))) : (((x78 - x37) ≥ 1) ∨ (x78 ≤ x38)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x37) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x38) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9020 (t x37 x38 x78 : ℝ) (h : (((x37 ≤ x38) ∧ (x38 ≤ x78) ∧ ((x78 - x37) ≥ 1) ∧ ((x38 - x37) ≤ (t - 1)) ∧ ((x78 - x38) ≤ (t - 1))) ∨ ((x78 ≤ x38) ∧ (x38 ≤ x37) ∧ ((x37 - x78) ≥ 1) ∧ ((x37 - x38) ≤ (t - 1)) ∧ ((x38 - x78) ≤ (t - 1))))) : (((x78 - x37) ≥ 1) ∨ (x38 ≤ x37)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x37) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x37) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9021 (t x37 x38 x78 : ℝ) (h : (((x37 ≤ x38) ∧ (x38 ≤ x78) ∧ ((x78 - x37) ≥ 1) ∧ ((x38 - x37) ≤ (t - 1)) ∧ ((x78 - x38) ≤ (t - 1))) ∨ ((x78 ≤ x38) ∧ (x38 ≤ x37) ∧ ((x37 - x78) ≥ 1) ∧ ((x37 - x38) ≤ (t - 1)) ∧ ((x38 - x78) ≤ (t - 1))))) : (((x78 - x37) ≥ 1) ∨ ((x37 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x37) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9022 (t x37 x38 x78 : ℝ) (h : (((x37 ≤ x38) ∧ (x38 ≤ x78) ∧ ((x78 - x37) ≥ 1) ∧ ((x38 - x37) ≤ (t - 1)) ∧ ((x78 - x38) ≤ (t - 1))) ∨ ((x78 ≤ x38) ∧ (x38 ≤ x37) ∧ ((x37 - x78) ≥ 1) ∧ ((x37 - x38) ≤ (t - 1)) ∧ ((x38 - x78) ≤ (t - 1))))) : (((x78 - x37) ≥ 1) ∨ ((x37 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x37) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9023 (t x37 x38 x78 : ℝ) (h : (((x37 ≤ x38) ∧ (x38 ≤ x78) ∧ ((x78 - x37) ≥ 1) ∧ ((x38 - x37) ≤ (t - 1)) ∧ ((x78 - x38) ≤ (t - 1))) ∨ ((x78 ≤ x38) ∧ (x38 ≤ x37) ∧ ((x37 - x78) ≥ 1) ∧ ((x37 - x38) ≤ (t - 1)) ∧ ((x38 - x78) ≤ (t - 1))))) : (((x78 - x37) ≥ 1) ∨ ((x38 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x37) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9024 (t x37 x38 x78 : ℝ) (h : (((x37 ≤ x38) ∧ (x38 ≤ x78) ∧ ((x78 - x37) ≥ 1) ∧ ((x38 - x37) ≤ (t - 1)) ∧ ((x78 - x38) ≤ (t - 1))) ∨ ((x78 ≤ x38) ∧ (x38 ≤ x37) ∧ ((x37 - x78) ≥ 1) ∧ ((x37 - x38) ≤ (t - 1)) ∧ ((x38 - x78) ≤ (t - 1))))) : (((x38 - x37) ≤ (t - 1)) ∨ (x78 ≤ x38)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x37) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x38) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9025 (t x37 x38 x78 : ℝ) (h : (((x37 ≤ x38) ∧ (x38 ≤ x78) ∧ ((x78 - x37) ≥ 1) ∧ ((x38 - x37) ≤ (t - 1)) ∧ ((x78 - x38) ≤ (t - 1))) ∨ ((x78 ≤ x38) ∧ (x38 ≤ x37) ∧ ((x37 - x78) ≥ 1) ∧ ((x37 - x38) ≤ (t - 1)) ∧ ((x38 - x78) ≤ (t - 1))))) : (((x38 - x37) ≤ (t - 1)) ∨ (x38 ≤ x37)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x37) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x37) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9026 (t x37 x38 x78 : ℝ) (h : (((x37 ≤ x38) ∧ (x38 ≤ x78) ∧ ((x78 - x37) ≥ 1) ∧ ((x38 - x37) ≤ (t - 1)) ∧ ((x78 - x38) ≤ (t - 1))) ∨ ((x78 ≤ x38) ∧ (x38 ≤ x37) ∧ ((x37 - x78) ≥ 1) ∧ ((x37 - x38) ≤ (t - 1)) ∧ ((x38 - x78) ≤ (t - 1))))) : (((x38 - x37) ≤ (t - 1)) ∨ ((x37 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x37) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9027 (t x37 x38 x78 : ℝ) (h : (((x37 ≤ x38) ∧ (x38 ≤ x78) ∧ ((x78 - x37) ≥ 1) ∧ ((x38 - x37) ≤ (t - 1)) ∧ ((x78 - x38) ≤ (t - 1))) ∨ ((x78 ≤ x38) ∧ (x38 ≤ x37) ∧ ((x37 - x78) ≥ 1) ∧ ((x37 - x38) ≤ (t - 1)) ∧ ((x38 - x78) ≤ (t - 1))))) : (((x38 - x37) ≤ (t - 1)) ∨ ((x37 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x37) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9028 (t x37 x38 x78 : ℝ) (h : (((x37 ≤ x38) ∧ (x38 ≤ x78) ∧ ((x78 - x37) ≥ 1) ∧ ((x38 - x37) ≤ (t - 1)) ∧ ((x78 - x38) ≤ (t - 1))) ∨ ((x78 ≤ x38) ∧ (x38 ≤ x37) ∧ ((x37 - x78) ≥ 1) ∧ ((x37 - x38) ≤ (t - 1)) ∧ ((x38 - x78) ≤ (t - 1))))) : (((x38 - x37) ≤ (t - 1)) ∨ ((x38 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x37) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9029 (t x37 x38 x78 : ℝ) (h : (((x37 ≤ x38) ∧ (x38 ≤ x78) ∧ ((x78 - x37) ≥ 1) ∧ ((x38 - x37) ≤ (t - 1)) ∧ ((x78 - x38) ≤ (t - 1))) ∨ ((x78 ≤ x38) ∧ (x38 ≤ x37) ∧ ((x37 - x78) ≥ 1) ∧ ((x37 - x38) ≤ (t - 1)) ∧ ((x38 - x78) ≤ (t - 1))))) : (((x78 - x38) ≤ (t - 1)) ∨ (x78 ≤ x38)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x38) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x38) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9030 (t x37 x38 x78 : ℝ) (h : (((x37 ≤ x38) ∧ (x38 ≤ x78) ∧ ((x78 - x37) ≥ 1) ∧ ((x38 - x37) ≤ (t - 1)) ∧ ((x78 - x38) ≤ (t - 1))) ∨ ((x78 ≤ x38) ∧ (x38 ≤ x37) ∧ ((x37 - x78) ≥ 1) ∧ ((x37 - x38) ≤ (t - 1)) ∧ ((x38 - x78) ≤ (t - 1))))) : (((x78 - x38) ≤ (t - 1)) ∨ (x38 ≤ x37)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x38) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x37) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9031 (t x37 x38 x78 : ℝ) (h : (((x37 ≤ x38) ∧ (x38 ≤ x78) ∧ ((x78 - x37) ≥ 1) ∧ ((x38 - x37) ≤ (t - 1)) ∧ ((x78 - x38) ≤ (t - 1))) ∨ ((x78 ≤ x38) ∧ (x38 ≤ x37) ∧ ((x37 - x78) ≥ 1) ∧ ((x37 - x38) ≤ (t - 1)) ∧ ((x38 - x78) ≤ (t - 1))))) : (((x78 - x38) ≤ (t - 1)) ∨ ((x37 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x38) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9032 (t x37 x38 x78 : ℝ) (h : (((x37 ≤ x38) ∧ (x38 ≤ x78) ∧ ((x78 - x37) ≥ 1) ∧ ((x38 - x37) ≤ (t - 1)) ∧ ((x78 - x38) ≤ (t - 1))) ∨ ((x78 ≤ x38) ∧ (x38 ≤ x37) ∧ ((x37 - x78) ≥ 1) ∧ ((x37 - x38) ≤ (t - 1)) ∧ ((x38 - x78) ≤ (t - 1))))) : (((x78 - x38) ≤ (t - 1)) ∨ ((x37 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x38) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9033 (t x37 x38 x78 : ℝ) (h : (((x37 ≤ x38) ∧ (x38 ≤ x78) ∧ ((x78 - x37) ≥ 1) ∧ ((x38 - x37) ≤ (t - 1)) ∧ ((x78 - x38) ≤ (t - 1))) ∨ ((x78 ≤ x38) ∧ (x38 ≤ x37) ∧ ((x37 - x78) ≥ 1) ∧ ((x37 - x38) ≤ (t - 1)) ∧ ((x38 - x78) ≤ (t - 1))))) : (((x78 - x38) ≤ (t - 1)) ∨ ((x38 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x38) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9034 (t x01 x13 x17 x37 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ ((t + ((-1) * x37)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x37)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th696 t x01 x13 x17 x37 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u0 (And.intro u1 (And.intro u5 u6)))))))) h

theorem clause9035 (t x37 : ℝ) : ((¬ ((t + ((-1) * x37)) ≤ 0)) ∨ (t ≤ x37)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x37)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x37) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th697 t x37
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause9037 (t x37 : ℝ) : ((¬ (t ≤ x37)) ∨ (¬ (x37 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x37 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th698 t x37
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause9039 (t x37 : ℝ) (h : (x37 < t)) : ((x37 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x37 < t) := fun hh => hn hh
  exact u0 h

theorem clause9040 (t x56 x57 x67 : ℝ) : ((¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x56 ≥ 0)) ∨ ((t + ((-1) * x57) + x67) ≥ 1) ∨ ((t + ((-1) * x57)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x57) + x67) ≥ 1) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th701 t x56 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u2 u1))))) h

theorem clause9042 (t x57 x58 x78 : ℝ) : (((t + ((-1) * x58)) ≤ 0) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ ((t + ((-1) * x58) + x78) ≥ 1) ∨ (¬ (x57 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x58)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x58) + x78) ≥ 1) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x57 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th703 t x57 x58 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u1 u0))))) h

theorem clause9043 (t x47 : ℝ) : ((¬ ((t + ((-1) * x47)) ≤ 0)) ∨ (t ≤ x47)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x47)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x47) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th704 t x47
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause9045 (t x47 : ℝ) : ((¬ (t ≤ x47)) ∨ (¬ (x47 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x47 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th705 t x47
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause9047 (t x47 : ℝ) (h : (x47 < t)) : ((x47 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x47 < t) := fun hh => hn hh
  exact u0 h

theorem clause9048 (x04 x34 x47 : ℝ) : ((¬ ((x04 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th708 x04 x34 x47
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u0 u2))) h

theorem clause9049 (x04 x34 x45 : ℝ) : ((¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x34)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th709 x04 x34 x45
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u1 u2))) h

theorem clause9050 (x35 x57 x58 : ℝ) : ((¬ ((x35 + ((-1) * x58)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x58)) ≥ 0)) ∨ ((x35 + ((-1) * x57)) ≤ (-1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x57 + ((-1) * x58)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x35 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th711 x35 x57 x58
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause9051 (x27 : ℝ) (h : (x27 ≥ 0)) : ((x27 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause9052 (t x01 x03 x12 x13 x14 x34 x45 x47 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x45 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x12) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x45 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th719 t x01 x03 x12 x13 x14 x34 x45 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u8 (And.intro u6 u7)))))))))) h

theorem clause9053 (t x24 x27 x47 : ℝ) : (((x24 + ((-1) * x27)) ≤ 0) ∨ ((x27 + ((-1) * x47)) ≥ 0) ∨ (¬ (x24 ≤ x27)) ∨ (¬ (x27 ≤ x47)) ∨ (¬ ((x47 - x24) ≥ 1)) ∨ (¬ ((x27 - x24) ≤ (t - 1))) ∨ (¬ ((x47 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x47)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th722 t x24 x27 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9054 (t x24 x27 x47 : ℝ) : (((x24 + ((-1) * x27)) ≤ 0) ∨ ((x24 + ((-1) * x27)) ≥ 0) ∨ (¬ (x24 ≤ x27)) ∨ (¬ (x27 ≤ x47)) ∨ (¬ ((x47 - x24) ≥ 1)) ∨ (¬ ((x27 - x24) ≤ (t - 1))) ∨ (¬ ((x47 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x27)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th722 t x24 x27 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9055 (t x24 x27 x47 : ℝ) : (((x24 + ((-1) * x47)) ≥ 1) ∨ ((x24 + ((-1) * x27)) ≤ 0) ∨ (¬ (x24 ≤ x27)) ∨ (¬ (x27 ≤ x47)) ∨ (¬ ((x47 - x24) ≥ 1)) ∨ (¬ ((x27 - x24) ≤ (t - 1))) ∨ (¬ ((x47 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th722 t x24 x27 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9056 (t x24 x27 x47 : ℝ) : (((x24 + ((-1) * x27)) ≤ 0) ∨ ((t + ((-1) * x24) + x27) ≥ 1) ∨ (¬ (x24 ≤ x27)) ∨ (¬ (x27 ≤ x47)) ∨ (¬ ((x47 - x24) ≥ 1)) ∨ (¬ ((x27 - x24) ≤ (t - 1))) ∨ (¬ ((x47 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x24) + x27) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th722 t x24 x27 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9059 (t x24 x27 x47 : ℝ) : (((x27 + ((-1) * x47)) ≤ 0) ∨ ((x24 + ((-1) * x27)) ≥ 0) ∨ (¬ (x24 ≤ x27)) ∨ (¬ (x27 ≤ x47)) ∨ (¬ ((x47 - x24) ≥ 1)) ∨ (¬ ((x27 - x24) ≤ (t - 1))) ∨ (¬ ((x47 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x27)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th722 t x24 x27 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9060 (t x24 x27 x47 : ℝ) : (((x24 + ((-1) * x47)) ≥ 1) ∨ ((x27 + ((-1) * x47)) ≤ 0) ∨ (¬ (x24 ≤ x27)) ∨ (¬ (x27 ≤ x47)) ∨ (¬ ((x47 - x24) ≥ 1)) ∨ (¬ ((x27 - x24) ≤ (t - 1))) ∨ (¬ ((x47 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th722 t x24 x27 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9063 (t x24 x27 x47 : ℝ) : (((x24 + ((-1) * x47)) ≤ (-1)) ∨ ((x27 + ((-1) * x47)) ≥ 0) ∨ (¬ (x24 ≤ x27)) ∨ (¬ (x27 ≤ x47)) ∨ (¬ ((x47 - x24) ≥ 1)) ∨ (¬ ((x27 - x24) ≤ (t - 1))) ∨ (¬ ((x47 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x47)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th722 t x24 x27 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9064 (t x24 x27 x47 : ℝ) : (((x24 + ((-1) * x47)) ≤ (-1)) ∨ ((x24 + ((-1) * x27)) ≥ 0) ∨ (¬ (x24 ≤ x27)) ∨ (¬ (x27 ≤ x47)) ∨ (¬ ((x47 - x24) ≥ 1)) ∨ (¬ ((x27 - x24) ≤ (t - 1))) ∨ (¬ ((x47 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x27)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th722 t x24 x27 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9065 (t x24 x27 x47 : ℝ) : (((x24 + ((-1) * x47)) ≤ (-1)) ∨ ((x24 + ((-1) * x47)) ≥ 1) ∨ (¬ (x24 ≤ x27)) ∨ (¬ (x27 ≤ x47)) ∨ (¬ ((x47 - x24) ≥ 1)) ∨ (¬ ((x27 - x24) ≤ (t - 1))) ∨ (¬ ((x47 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th722 t x24 x27 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9067 (t x24 x27 x47 : ℝ) : (((x24 + ((-1) * x47)) ≤ (-1)) ∨ ((t + ((-1) * x27) + x47) ≥ 1) ∨ (¬ (x24 ≤ x27)) ∨ (¬ (x27 ≤ x47)) ∨ (¬ ((x47 - x24) ≥ 1)) ∨ (¬ ((x27 - x24) ≤ (t - 1))) ∨ (¬ ((x47 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x27) + x47) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th722 t x24 x27 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9075 (t x24 x27 x47 : ℝ) : (((x24 + ((-1) * x47)) ≥ 1) ∨ ((t + x27 + ((-1) * x47)) ≥ 1) ∨ (¬ (x24 ≤ x27)) ∨ (¬ (x27 ≤ x47)) ∨ (¬ ((x47 - x24) ≥ 1)) ∨ (¬ ((x27 - x24) ≤ (t - 1))) ∨ (¬ ((x47 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x27 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th722 t x24 x27 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9078 (t x24 x27 x47 : ℝ) : (((x24 + ((-1) * x27)) ≤ 0) ∨ ((x27 + ((-1) * x47)) ≥ 0) ∨ (¬ (x47 ≤ x27)) ∨ (¬ (x27 ≤ x24)) ∨ (¬ ((x24 - x47) ≥ 1)) ∨ (¬ ((x24 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x47)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th722 t x24 x27 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9079 (t x24 x27 x47 : ℝ) : (((x24 + ((-1) * x27)) ≤ 0) ∨ ((x24 + ((-1) * x27)) ≥ 0) ∨ (¬ (x47 ≤ x27)) ∨ (¬ (x27 ≤ x24)) ∨ (¬ ((x24 - x47) ≥ 1)) ∨ (¬ ((x24 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x27)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th722 t x24 x27 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9080 (t x24 x27 x47 : ℝ) : (((x24 + ((-1) * x47)) ≥ 1) ∨ ((x24 + ((-1) * x27)) ≤ 0) ∨ (¬ (x47 ≤ x27)) ∨ (¬ (x27 ≤ x24)) ∨ (¬ ((x24 - x47) ≥ 1)) ∨ (¬ ((x24 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th722 t x24 x27 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9085 (t x24 x27 x47 : ℝ) : (((x24 + ((-1) * x47)) ≥ 1) ∨ ((x27 + ((-1) * x47)) ≤ 0) ∨ (¬ (x47 ≤ x27)) ∨ (¬ (x27 ≤ x24)) ∨ (¬ ((x24 - x47) ≥ 1)) ∨ (¬ ((x24 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th722 t x24 x27 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9088 (t x24 x27 x47 : ℝ) : (((x24 + ((-1) * x47)) ≤ (-1)) ∨ ((x27 + ((-1) * x47)) ≥ 0) ∨ (¬ (x47 ≤ x27)) ∨ (¬ (x27 ≤ x24)) ∨ (¬ ((x24 - x47) ≥ 1)) ∨ (¬ ((x24 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x47)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th722 t x24 x27 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9089 (t x24 x27 x47 : ℝ) : (((x24 + ((-1) * x47)) ≤ (-1)) ∨ ((x24 + ((-1) * x27)) ≥ 0) ∨ (¬ (x47 ≤ x27)) ∨ (¬ (x27 ≤ x24)) ∨ (¬ ((x24 - x47) ≥ 1)) ∨ (¬ ((x24 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x27)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th722 t x24 x27 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9090 (t x24 x27 x47 : ℝ) : (((x24 + ((-1) * x47)) ≤ (-1)) ∨ ((x24 + ((-1) * x47)) ≥ 1) ∨ (¬ (x47 ≤ x27)) ∨ (¬ (x27 ≤ x24)) ∨ (¬ ((x24 - x47) ≥ 1)) ∨ (¬ ((x24 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th722 t x24 x27 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9091 (t x24 x27 x47 : ℝ) : (((x24 + ((-1) * x47)) ≤ (-1)) ∨ ((t + ((-1) * x24) + x27) ≥ 1) ∨ (¬ (x47 ≤ x27)) ∨ (¬ (x27 ≤ x24)) ∨ (¬ ((x24 - x47) ≥ 1)) ∨ (¬ ((x24 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x24) + x27) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th722 t x24 x27 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9092 (t x24 x27 x47 : ℝ) : (((x24 + ((-1) * x47)) ≤ (-1)) ∨ ((t + ((-1) * x27) + x47) ≥ 1) ∨ (¬ (x47 ≤ x27)) ∨ (¬ (x27 ≤ x24)) ∨ (¬ ((x24 - x47) ≥ 1)) ∨ (¬ ((x24 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x27) + x47) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th722 t x24 x27 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9100 (t x24 x27 x47 : ℝ) : (((x24 + ((-1) * x47)) ≥ 1) ∨ ((t + x27 + ((-1) * x47)) ≥ 1) ∨ (¬ (x47 ≤ x27)) ∨ (¬ (x27 ≤ x24)) ∨ (¬ ((x24 - x47) ≥ 1)) ∨ (¬ ((x24 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x27 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th722 t x24 x27 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9153 (t x24 x27 x47 : ℝ) (h : (((x24 ≤ x27) ∧ (x27 ≤ x47) ∧ ((x47 - x24) ≥ 1) ∧ ((x27 - x24) ≤ (t - 1)) ∧ ((x47 - x27) ≤ (t - 1))) ∨ ((x47 ≤ x27) ∧ (x27 ≤ x24) ∧ ((x24 - x47) ≥ 1) ∧ ((x24 - x27) ≤ (t - 1)) ∧ ((x27 - x47) ≤ (t - 1))))) : ((x24 ≤ x27) ∨ (x47 ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x27) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9154 (t x24 x27 x47 : ℝ) (h : (((x24 ≤ x27) ∧ (x27 ≤ x47) ∧ ((x47 - x24) ≥ 1) ∧ ((x27 - x24) ≤ (t - 1)) ∧ ((x47 - x27) ≤ (t - 1))) ∨ ((x47 ≤ x27) ∧ (x27 ≤ x24) ∧ ((x24 - x47) ≥ 1) ∧ ((x24 - x27) ≤ (t - 1)) ∧ ((x27 - x47) ≤ (t - 1))))) : ((x24 ≤ x27) ∨ (x27 ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x24) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9155 (t x24 x27 x47 : ℝ) (h : (((x24 ≤ x27) ∧ (x27 ≤ x47) ∧ ((x47 - x24) ≥ 1) ∧ ((x27 - x24) ≤ (t - 1)) ∧ ((x47 - x27) ≤ (t - 1))) ∨ ((x47 ≤ x27) ∧ (x27 ≤ x24) ∧ ((x24 - x47) ≥ 1) ∧ ((x24 - x27) ≤ (t - 1)) ∧ ((x27 - x47) ≤ (t - 1))))) : ((x24 ≤ x27) ∨ ((x24 - x47) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x47) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9156 (t x24 x27 x47 : ℝ) (h : (((x24 ≤ x27) ∧ (x27 ≤ x47) ∧ ((x47 - x24) ≥ 1) ∧ ((x27 - x24) ≤ (t - 1)) ∧ ((x47 - x27) ≤ (t - 1))) ∨ ((x47 ≤ x27) ∧ (x27 ≤ x24) ∧ ((x24 - x47) ≥ 1) ∧ ((x24 - x27) ≤ (t - 1)) ∧ ((x27 - x47) ≤ (t - 1))))) : ((x24 ≤ x27) ∨ ((x24 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9157 (t x24 x27 x47 : ℝ) (h : (((x24 ≤ x27) ∧ (x27 ≤ x47) ∧ ((x47 - x24) ≥ 1) ∧ ((x27 - x24) ≤ (t - 1)) ∧ ((x47 - x27) ≤ (t - 1))) ∨ ((x47 ≤ x27) ∧ (x27 ≤ x24) ∧ ((x24 - x47) ≥ 1) ∧ ((x24 - x27) ≤ (t - 1)) ∧ ((x27 - x47) ≤ (t - 1))))) : ((x24 ≤ x27) ∨ ((x27 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9158 (t x24 x27 x47 : ℝ) (h : (((x24 ≤ x27) ∧ (x27 ≤ x47) ∧ ((x47 - x24) ≥ 1) ∧ ((x27 - x24) ≤ (t - 1)) ∧ ((x47 - x27) ≤ (t - 1))) ∨ ((x47 ≤ x27) ∧ (x27 ≤ x24) ∧ ((x24 - x47) ≥ 1) ∧ ((x24 - x27) ≤ (t - 1)) ∧ ((x27 - x47) ≤ (t - 1))))) : ((x27 ≤ x47) ∨ (x47 ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x27) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9159 (t x24 x27 x47 : ℝ) (h : (((x24 ≤ x27) ∧ (x27 ≤ x47) ∧ ((x47 - x24) ≥ 1) ∧ ((x27 - x24) ≤ (t - 1)) ∧ ((x47 - x27) ≤ (t - 1))) ∨ ((x47 ≤ x27) ∧ (x27 ≤ x24) ∧ ((x24 - x47) ≥ 1) ∧ ((x24 - x27) ≤ (t - 1)) ∧ ((x27 - x47) ≤ (t - 1))))) : ((x27 ≤ x47) ∨ (x27 ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x24) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9160 (t x24 x27 x47 : ℝ) (h : (((x24 ≤ x27) ∧ (x27 ≤ x47) ∧ ((x47 - x24) ≥ 1) ∧ ((x27 - x24) ≤ (t - 1)) ∧ ((x47 - x27) ≤ (t - 1))) ∨ ((x47 ≤ x27) ∧ (x27 ≤ x24) ∧ ((x24 - x47) ≥ 1) ∧ ((x24 - x27) ≤ (t - 1)) ∧ ((x27 - x47) ≤ (t - 1))))) : ((x27 ≤ x47) ∨ ((x24 - x47) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x47) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9161 (t x24 x27 x47 : ℝ) (h : (((x24 ≤ x27) ∧ (x27 ≤ x47) ∧ ((x47 - x24) ≥ 1) ∧ ((x27 - x24) ≤ (t - 1)) ∧ ((x47 - x27) ≤ (t - 1))) ∨ ((x47 ≤ x27) ∧ (x27 ≤ x24) ∧ ((x24 - x47) ≥ 1) ∧ ((x24 - x27) ≤ (t - 1)) ∧ ((x27 - x47) ≤ (t - 1))))) : ((x27 ≤ x47) ∨ ((x24 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9162 (t x24 x27 x47 : ℝ) (h : (((x24 ≤ x27) ∧ (x27 ≤ x47) ∧ ((x47 - x24) ≥ 1) ∧ ((x27 - x24) ≤ (t - 1)) ∧ ((x47 - x27) ≤ (t - 1))) ∨ ((x47 ≤ x27) ∧ (x27 ≤ x24) ∧ ((x24 - x47) ≥ 1) ∧ ((x24 - x27) ≤ (t - 1)) ∧ ((x27 - x47) ≤ (t - 1))))) : ((x27 ≤ x47) ∨ ((x27 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9163 (t x24 x27 x47 : ℝ) (h : (((x24 ≤ x27) ∧ (x27 ≤ x47) ∧ ((x47 - x24) ≥ 1) ∧ ((x27 - x24) ≤ (t - 1)) ∧ ((x47 - x27) ≤ (t - 1))) ∨ ((x47 ≤ x27) ∧ (x27 ≤ x24) ∧ ((x24 - x47) ≥ 1) ∧ ((x24 - x27) ≤ (t - 1)) ∧ ((x27 - x47) ≤ (t - 1))))) : (((x47 - x24) ≥ 1) ∨ (x47 ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x24) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x27) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9164 (t x24 x27 x47 : ℝ) (h : (((x24 ≤ x27) ∧ (x27 ≤ x47) ∧ ((x47 - x24) ≥ 1) ∧ ((x27 - x24) ≤ (t - 1)) ∧ ((x47 - x27) ≤ (t - 1))) ∨ ((x47 ≤ x27) ∧ (x27 ≤ x24) ∧ ((x24 - x47) ≥ 1) ∧ ((x24 - x27) ≤ (t - 1)) ∧ ((x27 - x47) ≤ (t - 1))))) : (((x47 - x24) ≥ 1) ∨ (x27 ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x24) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x24) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9165 (t x24 x27 x47 : ℝ) (h : (((x24 ≤ x27) ∧ (x27 ≤ x47) ∧ ((x47 - x24) ≥ 1) ∧ ((x27 - x24) ≤ (t - 1)) ∧ ((x47 - x27) ≤ (t - 1))) ∨ ((x47 ≤ x27) ∧ (x27 ≤ x24) ∧ ((x24 - x47) ≥ 1) ∧ ((x24 - x27) ≤ (t - 1)) ∧ ((x27 - x47) ≤ (t - 1))))) : (((x47 - x24) ≥ 1) ∨ ((x24 - x47) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x24) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x47) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9166 (t x24 x27 x47 : ℝ) (h : (((x24 ≤ x27) ∧ (x27 ≤ x47) ∧ ((x47 - x24) ≥ 1) ∧ ((x27 - x24) ≤ (t - 1)) ∧ ((x47 - x27) ≤ (t - 1))) ∨ ((x47 ≤ x27) ∧ (x27 ≤ x24) ∧ ((x24 - x47) ≥ 1) ∧ ((x24 - x27) ≤ (t - 1)) ∧ ((x27 - x47) ≤ (t - 1))))) : (((x47 - x24) ≥ 1) ∨ ((x24 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x24) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9167 (t x24 x27 x47 : ℝ) (h : (((x24 ≤ x27) ∧ (x27 ≤ x47) ∧ ((x47 - x24) ≥ 1) ∧ ((x27 - x24) ≤ (t - 1)) ∧ ((x47 - x27) ≤ (t - 1))) ∨ ((x47 ≤ x27) ∧ (x27 ≤ x24) ∧ ((x24 - x47) ≥ 1) ∧ ((x24 - x27) ≤ (t - 1)) ∧ ((x27 - x47) ≤ (t - 1))))) : (((x47 - x24) ≥ 1) ∨ ((x27 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x24) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9168 (t x24 x27 x47 : ℝ) (h : (((x24 ≤ x27) ∧ (x27 ≤ x47) ∧ ((x47 - x24) ≥ 1) ∧ ((x27 - x24) ≤ (t - 1)) ∧ ((x47 - x27) ≤ (t - 1))) ∨ ((x47 ≤ x27) ∧ (x27 ≤ x24) ∧ ((x24 - x47) ≥ 1) ∧ ((x24 - x27) ≤ (t - 1)) ∧ ((x27 - x47) ≤ (t - 1))))) : (((x27 - x24) ≤ (t - 1)) ∨ (x47 ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x24) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x27) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9169 (t x24 x27 x47 : ℝ) (h : (((x24 ≤ x27) ∧ (x27 ≤ x47) ∧ ((x47 - x24) ≥ 1) ∧ ((x27 - x24) ≤ (t - 1)) ∧ ((x47 - x27) ≤ (t - 1))) ∨ ((x47 ≤ x27) ∧ (x27 ≤ x24) ∧ ((x24 - x47) ≥ 1) ∧ ((x24 - x27) ≤ (t - 1)) ∧ ((x27 - x47) ≤ (t - 1))))) : (((x27 - x24) ≤ (t - 1)) ∨ (x27 ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x24) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x24) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9170 (t x24 x27 x47 : ℝ) (h : (((x24 ≤ x27) ∧ (x27 ≤ x47) ∧ ((x47 - x24) ≥ 1) ∧ ((x27 - x24) ≤ (t - 1)) ∧ ((x47 - x27) ≤ (t - 1))) ∨ ((x47 ≤ x27) ∧ (x27 ≤ x24) ∧ ((x24 - x47) ≥ 1) ∧ ((x24 - x27) ≤ (t - 1)) ∧ ((x27 - x47) ≤ (t - 1))))) : (((x27 - x24) ≤ (t - 1)) ∨ ((x24 - x47) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x24) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x47) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9171 (t x24 x27 x47 : ℝ) (h : (((x24 ≤ x27) ∧ (x27 ≤ x47) ∧ ((x47 - x24) ≥ 1) ∧ ((x27 - x24) ≤ (t - 1)) ∧ ((x47 - x27) ≤ (t - 1))) ∨ ((x47 ≤ x27) ∧ (x27 ≤ x24) ∧ ((x24 - x47) ≥ 1) ∧ ((x24 - x27) ≤ (t - 1)) ∧ ((x27 - x47) ≤ (t - 1))))) : (((x27 - x24) ≤ (t - 1)) ∨ ((x24 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x24) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9172 (t x24 x27 x47 : ℝ) (h : (((x24 ≤ x27) ∧ (x27 ≤ x47) ∧ ((x47 - x24) ≥ 1) ∧ ((x27 - x24) ≤ (t - 1)) ∧ ((x47 - x27) ≤ (t - 1))) ∨ ((x47 ≤ x27) ∧ (x27 ≤ x24) ∧ ((x24 - x47) ≥ 1) ∧ ((x24 - x27) ≤ (t - 1)) ∧ ((x27 - x47) ≤ (t - 1))))) : (((x27 - x24) ≤ (t - 1)) ∨ ((x27 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x24) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9173 (t x24 x27 x47 : ℝ) (h : (((x24 ≤ x27) ∧ (x27 ≤ x47) ∧ ((x47 - x24) ≥ 1) ∧ ((x27 - x24) ≤ (t - 1)) ∧ ((x47 - x27) ≤ (t - 1))) ∨ ((x47 ≤ x27) ∧ (x27 ≤ x24) ∧ ((x24 - x47) ≥ 1) ∧ ((x24 - x27) ≤ (t - 1)) ∧ ((x27 - x47) ≤ (t - 1))))) : (((x47 - x27) ≤ (t - 1)) ∨ (x47 ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x27) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x27) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9174 (t x24 x27 x47 : ℝ) (h : (((x24 ≤ x27) ∧ (x27 ≤ x47) ∧ ((x47 - x24) ≥ 1) ∧ ((x27 - x24) ≤ (t - 1)) ∧ ((x47 - x27) ≤ (t - 1))) ∨ ((x47 ≤ x27) ∧ (x27 ≤ x24) ∧ ((x24 - x47) ≥ 1) ∧ ((x24 - x27) ≤ (t - 1)) ∧ ((x27 - x47) ≤ (t - 1))))) : (((x47 - x27) ≤ (t - 1)) ∨ (x27 ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x27) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x24) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9175 (t x24 x27 x47 : ℝ) (h : (((x24 ≤ x27) ∧ (x27 ≤ x47) ∧ ((x47 - x24) ≥ 1) ∧ ((x27 - x24) ≤ (t - 1)) ∧ ((x47 - x27) ≤ (t - 1))) ∨ ((x47 ≤ x27) ∧ (x27 ≤ x24) ∧ ((x24 - x47) ≥ 1) ∧ ((x24 - x27) ≤ (t - 1)) ∧ ((x27 - x47) ≤ (t - 1))))) : (((x47 - x27) ≤ (t - 1)) ∨ ((x24 - x47) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x27) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x47) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9176 (t x24 x27 x47 : ℝ) (h : (((x24 ≤ x27) ∧ (x27 ≤ x47) ∧ ((x47 - x24) ≥ 1) ∧ ((x27 - x24) ≤ (t - 1)) ∧ ((x47 - x27) ≤ (t - 1))) ∨ ((x47 ≤ x27) ∧ (x27 ≤ x24) ∧ ((x24 - x47) ≥ 1) ∧ ((x24 - x27) ≤ (t - 1)) ∧ ((x27 - x47) ≤ (t - 1))))) : (((x47 - x27) ≤ (t - 1)) ∨ ((x24 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x27) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9177 (t x24 x27 x47 : ℝ) (h : (((x24 ≤ x27) ∧ (x27 ≤ x47) ∧ ((x47 - x24) ≥ 1) ∧ ((x27 - x24) ≤ (t - 1)) ∧ ((x47 - x27) ≤ (t - 1))) ∨ ((x47 ≤ x27) ∧ (x27 ≤ x24) ∧ ((x24 - x47) ≥ 1) ∧ ((x24 - x27) ≤ (t - 1)) ∧ ((x27 - x47) ≤ (t - 1))))) : (((x47 - x27) ≤ (t - 1)) ∨ ((x27 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x27) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9185 (t x27 x28 x78 : ℝ) : (((x27 + ((-1) * x78)) ≥ 1) ∨ ((x28 + ((-1) * x78)) ≤ 0) ∨ (¬ (x27 ≤ x28)) ∨ (¬ (x28 ≤ x78)) ∨ (¬ ((x78 - x27) ≥ 1)) ∨ (¬ ((x28 - x27) ≤ (t - 1))) ∨ (¬ ((x78 - x28) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x27 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x27) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x28 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th727 t x27 x28 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9190 (t x27 x28 x78 : ℝ) : (((x27 + ((-1) * x78)) ≤ (-1)) ∨ ((x27 + ((-1) * x78)) ≥ 1) ∨ (¬ (x27 ≤ x28)) ∨ (¬ (x28 ≤ x78)) ∨ (¬ ((x78 - x27) ≥ 1)) ∨ (¬ ((x28 - x27) ≤ (t - 1))) ∨ (¬ ((x78 - x28) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x27 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x27) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x28 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th727 t x27 x28 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9192 (t x27 x28 x78 : ℝ) : (((x27 + ((-1) * x78)) ≤ (-1)) ∨ ((t + ((-1) * x28) + x78) ≥ 1) ∨ (¬ (x27 ≤ x28)) ∨ (¬ (x28 ≤ x78)) ∨ (¬ ((x78 - x27) ≥ 1)) ∨ (¬ ((x28 - x27) ≤ (t - 1))) ∨ (¬ ((x78 - x28) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x28) + x78) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x27 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x27) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x28 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th727 t x27 x28 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9200 (t x27 x28 x78 : ℝ) : (((x27 + ((-1) * x78)) ≥ 1) ∨ ((t + x28 + ((-1) * x78)) ≥ 1) ∨ (¬ (x27 ≤ x28)) ∨ (¬ (x28 ≤ x78)) ∨ (¬ ((x78 - x27) ≥ 1)) ∨ (¬ ((x28 - x27) ≤ (t - 1))) ∨ (¬ ((x78 - x28) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x28 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x27 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x27) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x28 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th727 t x27 x28 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9210 (t x27 x28 x78 : ℝ) : (((x27 + ((-1) * x78)) ≥ 1) ∨ ((x28 + ((-1) * x78)) ≤ 0) ∨ (¬ (x78 ≤ x28)) ∨ (¬ (x28 ≤ x27)) ∨ (¬ ((x27 - x78) ≥ 1)) ∨ (¬ ((x27 - x28) ≤ (t - 1))) ∨ (¬ ((x28 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x28 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th727 t x27 x28 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9215 (t x27 x28 x78 : ℝ) : (((x27 + ((-1) * x78)) ≤ (-1)) ∨ ((x27 + ((-1) * x78)) ≥ 1) ∨ (¬ (x78 ≤ x28)) ∨ (¬ (x28 ≤ x27)) ∨ (¬ ((x27 - x78) ≥ 1)) ∨ (¬ ((x27 - x28) ≤ (t - 1))) ∨ (¬ ((x28 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x28 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th727 t x27 x28 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9217 (t x27 x28 x78 : ℝ) : (((x27 + ((-1) * x78)) ≤ (-1)) ∨ ((t + ((-1) * x28) + x78) ≥ 1) ∨ (¬ (x78 ≤ x28)) ∨ (¬ (x28 ≤ x27)) ∨ (¬ ((x27 - x78) ≥ 1)) ∨ (¬ ((x27 - x28) ≤ (t - 1))) ∨ (¬ ((x28 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x28) + x78) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x28 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th727 t x27 x28 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9225 (t x27 x28 x78 : ℝ) : (((x27 + ((-1) * x78)) ≥ 1) ∨ ((t + x28 + ((-1) * x78)) ≥ 1) ∨ (¬ (x78 ≤ x28)) ∨ (¬ (x28 ≤ x27)) ∨ (¬ ((x27 - x78) ≥ 1)) ∨ (¬ ((x27 - x28) ≤ (t - 1))) ∨ (¬ ((x28 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x28 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x28 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th727 t x27 x28 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9278 (t x27 x28 x78 : ℝ) (h : (((x27 ≤ x28) ∧ (x28 ≤ x78) ∧ ((x78 - x27) ≥ 1) ∧ ((x28 - x27) ≤ (t - 1)) ∧ ((x78 - x28) ≤ (t - 1))) ∨ ((x78 ≤ x28) ∧ (x28 ≤ x27) ∧ ((x27 - x78) ≥ 1) ∧ ((x27 - x28) ≤ (t - 1)) ∧ ((x28 - x78) ≤ (t - 1))))) : ((x27 ≤ x28) ∨ (x78 ≤ x28)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x28) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9279 (t x27 x28 x78 : ℝ) (h : (((x27 ≤ x28) ∧ (x28 ≤ x78) ∧ ((x78 - x27) ≥ 1) ∧ ((x28 - x27) ≤ (t - 1)) ∧ ((x78 - x28) ≤ (t - 1))) ∨ ((x78 ≤ x28) ∧ (x28 ≤ x27) ∧ ((x27 - x78) ≥ 1) ∧ ((x27 - x28) ≤ (t - 1)) ∧ ((x28 - x78) ≤ (t - 1))))) : ((x27 ≤ x28) ∨ (x28 ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x27) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9280 (t x27 x28 x78 : ℝ) (h : (((x27 ≤ x28) ∧ (x28 ≤ x78) ∧ ((x78 - x27) ≥ 1) ∧ ((x28 - x27) ≤ (t - 1)) ∧ ((x78 - x28) ≤ (t - 1))) ∨ ((x78 ≤ x28) ∧ (x28 ≤ x27) ∧ ((x27 - x78) ≥ 1) ∧ ((x27 - x28) ≤ (t - 1)) ∧ ((x28 - x78) ≤ (t - 1))))) : ((x27 ≤ x28) ∨ ((x27 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9281 (t x27 x28 x78 : ℝ) (h : (((x27 ≤ x28) ∧ (x28 ≤ x78) ∧ ((x78 - x27) ≥ 1) ∧ ((x28 - x27) ≤ (t - 1)) ∧ ((x78 - x28) ≤ (t - 1))) ∨ ((x78 ≤ x28) ∧ (x28 ≤ x27) ∧ ((x27 - x78) ≥ 1) ∧ ((x27 - x28) ≤ (t - 1)) ∧ ((x28 - x78) ≤ (t - 1))))) : ((x27 ≤ x28) ∨ ((x27 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9282 (t x27 x28 x78 : ℝ) (h : (((x27 ≤ x28) ∧ (x28 ≤ x78) ∧ ((x78 - x27) ≥ 1) ∧ ((x28 - x27) ≤ (t - 1)) ∧ ((x78 - x28) ≤ (t - 1))) ∨ ((x78 ≤ x28) ∧ (x28 ≤ x27) ∧ ((x27 - x78) ≥ 1) ∧ ((x27 - x28) ≤ (t - 1)) ∧ ((x28 - x78) ≤ (t - 1))))) : ((x27 ≤ x28) ∨ ((x28 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9283 (t x27 x28 x78 : ℝ) (h : (((x27 ≤ x28) ∧ (x28 ≤ x78) ∧ ((x78 - x27) ≥ 1) ∧ ((x28 - x27) ≤ (t - 1)) ∧ ((x78 - x28) ≤ (t - 1))) ∨ ((x78 ≤ x28) ∧ (x28 ≤ x27) ∧ ((x27 - x78) ≥ 1) ∧ ((x27 - x28) ≤ (t - 1)) ∧ ((x28 - x78) ≤ (t - 1))))) : ((x28 ≤ x78) ∨ (x78 ≤ x28)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x28 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x28) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9284 (t x27 x28 x78 : ℝ) (h : (((x27 ≤ x28) ∧ (x28 ≤ x78) ∧ ((x78 - x27) ≥ 1) ∧ ((x28 - x27) ≤ (t - 1)) ∧ ((x78 - x28) ≤ (t - 1))) ∨ ((x78 ≤ x28) ∧ (x28 ≤ x27) ∧ ((x27 - x78) ≥ 1) ∧ ((x27 - x28) ≤ (t - 1)) ∧ ((x28 - x78) ≤ (t - 1))))) : ((x28 ≤ x78) ∨ (x28 ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x28 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x27) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9285 (t x27 x28 x78 : ℝ) (h : (((x27 ≤ x28) ∧ (x28 ≤ x78) ∧ ((x78 - x27) ≥ 1) ∧ ((x28 - x27) ≤ (t - 1)) ∧ ((x78 - x28) ≤ (t - 1))) ∨ ((x78 ≤ x28) ∧ (x28 ≤ x27) ∧ ((x27 - x78) ≥ 1) ∧ ((x27 - x28) ≤ (t - 1)) ∧ ((x28 - x78) ≤ (t - 1))))) : ((x28 ≤ x78) ∨ ((x27 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x28 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9286 (t x27 x28 x78 : ℝ) (h : (((x27 ≤ x28) ∧ (x28 ≤ x78) ∧ ((x78 - x27) ≥ 1) ∧ ((x28 - x27) ≤ (t - 1)) ∧ ((x78 - x28) ≤ (t - 1))) ∨ ((x78 ≤ x28) ∧ (x28 ≤ x27) ∧ ((x27 - x78) ≥ 1) ∧ ((x27 - x28) ≤ (t - 1)) ∧ ((x28 - x78) ≤ (t - 1))))) : ((x28 ≤ x78) ∨ ((x27 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x28 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9287 (t x27 x28 x78 : ℝ) (h : (((x27 ≤ x28) ∧ (x28 ≤ x78) ∧ ((x78 - x27) ≥ 1) ∧ ((x28 - x27) ≤ (t - 1)) ∧ ((x78 - x28) ≤ (t - 1))) ∨ ((x78 ≤ x28) ∧ (x28 ≤ x27) ∧ ((x27 - x78) ≥ 1) ∧ ((x27 - x28) ≤ (t - 1)) ∧ ((x28 - x78) ≤ (t - 1))))) : ((x28 ≤ x78) ∨ ((x28 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x28 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9288 (t x27 x28 x78 : ℝ) (h : (((x27 ≤ x28) ∧ (x28 ≤ x78) ∧ ((x78 - x27) ≥ 1) ∧ ((x28 - x27) ≤ (t - 1)) ∧ ((x78 - x28) ≤ (t - 1))) ∨ ((x78 ≤ x28) ∧ (x28 ≤ x27) ∧ ((x27 - x78) ≥ 1) ∧ ((x27 - x28) ≤ (t - 1)) ∧ ((x28 - x78) ≤ (t - 1))))) : (((x78 - x27) ≥ 1) ∨ (x78 ≤ x28)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x27) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x28) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9289 (t x27 x28 x78 : ℝ) (h : (((x27 ≤ x28) ∧ (x28 ≤ x78) ∧ ((x78 - x27) ≥ 1) ∧ ((x28 - x27) ≤ (t - 1)) ∧ ((x78 - x28) ≤ (t - 1))) ∨ ((x78 ≤ x28) ∧ (x28 ≤ x27) ∧ ((x27 - x78) ≥ 1) ∧ ((x27 - x28) ≤ (t - 1)) ∧ ((x28 - x78) ≤ (t - 1))))) : (((x78 - x27) ≥ 1) ∨ (x28 ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x27) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x27) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9290 (t x27 x28 x78 : ℝ) (h : (((x27 ≤ x28) ∧ (x28 ≤ x78) ∧ ((x78 - x27) ≥ 1) ∧ ((x28 - x27) ≤ (t - 1)) ∧ ((x78 - x28) ≤ (t - 1))) ∨ ((x78 ≤ x28) ∧ (x28 ≤ x27) ∧ ((x27 - x78) ≥ 1) ∧ ((x27 - x28) ≤ (t - 1)) ∧ ((x28 - x78) ≤ (t - 1))))) : (((x78 - x27) ≥ 1) ∨ ((x27 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x27) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9291 (t x27 x28 x78 : ℝ) (h : (((x27 ≤ x28) ∧ (x28 ≤ x78) ∧ ((x78 - x27) ≥ 1) ∧ ((x28 - x27) ≤ (t - 1)) ∧ ((x78 - x28) ≤ (t - 1))) ∨ ((x78 ≤ x28) ∧ (x28 ≤ x27) ∧ ((x27 - x78) ≥ 1) ∧ ((x27 - x28) ≤ (t - 1)) ∧ ((x28 - x78) ≤ (t - 1))))) : (((x78 - x27) ≥ 1) ∨ ((x27 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x27) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9292 (t x27 x28 x78 : ℝ) (h : (((x27 ≤ x28) ∧ (x28 ≤ x78) ∧ ((x78 - x27) ≥ 1) ∧ ((x28 - x27) ≤ (t - 1)) ∧ ((x78 - x28) ≤ (t - 1))) ∨ ((x78 ≤ x28) ∧ (x28 ≤ x27) ∧ ((x27 - x78) ≥ 1) ∧ ((x27 - x28) ≤ (t - 1)) ∧ ((x28 - x78) ≤ (t - 1))))) : (((x78 - x27) ≥ 1) ∨ ((x28 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x27) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9293 (t x27 x28 x78 : ℝ) (h : (((x27 ≤ x28) ∧ (x28 ≤ x78) ∧ ((x78 - x27) ≥ 1) ∧ ((x28 - x27) ≤ (t - 1)) ∧ ((x78 - x28) ≤ (t - 1))) ∨ ((x78 ≤ x28) ∧ (x28 ≤ x27) ∧ ((x27 - x78) ≥ 1) ∧ ((x27 - x28) ≤ (t - 1)) ∧ ((x28 - x78) ≤ (t - 1))))) : (((x28 - x27) ≤ (t - 1)) ∨ (x78 ≤ x28)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x27) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x28) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9294 (t x27 x28 x78 : ℝ) (h : (((x27 ≤ x28) ∧ (x28 ≤ x78) ∧ ((x78 - x27) ≥ 1) ∧ ((x28 - x27) ≤ (t - 1)) ∧ ((x78 - x28) ≤ (t - 1))) ∨ ((x78 ≤ x28) ∧ (x28 ≤ x27) ∧ ((x27 - x78) ≥ 1) ∧ ((x27 - x28) ≤ (t - 1)) ∧ ((x28 - x78) ≤ (t - 1))))) : (((x28 - x27) ≤ (t - 1)) ∨ (x28 ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x27) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x27) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9295 (t x27 x28 x78 : ℝ) (h : (((x27 ≤ x28) ∧ (x28 ≤ x78) ∧ ((x78 - x27) ≥ 1) ∧ ((x28 - x27) ≤ (t - 1)) ∧ ((x78 - x28) ≤ (t - 1))) ∨ ((x78 ≤ x28) ∧ (x28 ≤ x27) ∧ ((x27 - x78) ≥ 1) ∧ ((x27 - x28) ≤ (t - 1)) ∧ ((x28 - x78) ≤ (t - 1))))) : (((x28 - x27) ≤ (t - 1)) ∨ ((x27 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x27) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9296 (t x27 x28 x78 : ℝ) (h : (((x27 ≤ x28) ∧ (x28 ≤ x78) ∧ ((x78 - x27) ≥ 1) ∧ ((x28 - x27) ≤ (t - 1)) ∧ ((x78 - x28) ≤ (t - 1))) ∨ ((x78 ≤ x28) ∧ (x28 ≤ x27) ∧ ((x27 - x78) ≥ 1) ∧ ((x27 - x28) ≤ (t - 1)) ∧ ((x28 - x78) ≤ (t - 1))))) : (((x28 - x27) ≤ (t - 1)) ∨ ((x27 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x27) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9297 (t x27 x28 x78 : ℝ) (h : (((x27 ≤ x28) ∧ (x28 ≤ x78) ∧ ((x78 - x27) ≥ 1) ∧ ((x28 - x27) ≤ (t - 1)) ∧ ((x78 - x28) ≤ (t - 1))) ∨ ((x78 ≤ x28) ∧ (x28 ≤ x27) ∧ ((x27 - x78) ≥ 1) ∧ ((x27 - x28) ≤ (t - 1)) ∧ ((x28 - x78) ≤ (t - 1))))) : (((x28 - x27) ≤ (t - 1)) ∨ ((x28 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x27) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9298 (t x27 x28 x78 : ℝ) (h : (((x27 ≤ x28) ∧ (x28 ≤ x78) ∧ ((x78 - x27) ≥ 1) ∧ ((x28 - x27) ≤ (t - 1)) ∧ ((x78 - x28) ≤ (t - 1))) ∨ ((x78 ≤ x28) ∧ (x28 ≤ x27) ∧ ((x27 - x78) ≥ 1) ∧ ((x27 - x28) ≤ (t - 1)) ∧ ((x28 - x78) ≤ (t - 1))))) : (((x78 - x28) ≤ (t - 1)) ∨ (x78 ≤ x28)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x28) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x28) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9299 (t x27 x28 x78 : ℝ) (h : (((x27 ≤ x28) ∧ (x28 ≤ x78) ∧ ((x78 - x27) ≥ 1) ∧ ((x28 - x27) ≤ (t - 1)) ∧ ((x78 - x28) ≤ (t - 1))) ∨ ((x78 ≤ x28) ∧ (x28 ≤ x27) ∧ ((x27 - x78) ≥ 1) ∧ ((x27 - x28) ≤ (t - 1)) ∧ ((x28 - x78) ≤ (t - 1))))) : (((x78 - x28) ≤ (t - 1)) ∨ (x28 ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x28) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x27) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9300 (t x27 x28 x78 : ℝ) (h : (((x27 ≤ x28) ∧ (x28 ≤ x78) ∧ ((x78 - x27) ≥ 1) ∧ ((x28 - x27) ≤ (t - 1)) ∧ ((x78 - x28) ≤ (t - 1))) ∨ ((x78 ≤ x28) ∧ (x28 ≤ x27) ∧ ((x27 - x78) ≥ 1) ∧ ((x27 - x28) ≤ (t - 1)) ∧ ((x28 - x78) ≤ (t - 1))))) : (((x78 - x28) ≤ (t - 1)) ∨ ((x27 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x28) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9301 (t x27 x28 x78 : ℝ) (h : (((x27 ≤ x28) ∧ (x28 ≤ x78) ∧ ((x78 - x27) ≥ 1) ∧ ((x28 - x27) ≤ (t - 1)) ∧ ((x78 - x28) ≤ (t - 1))) ∨ ((x78 ≤ x28) ∧ (x28 ≤ x27) ∧ ((x27 - x78) ≥ 1) ∧ ((x27 - x28) ≤ (t - 1)) ∧ ((x28 - x78) ≤ (t - 1))))) : (((x78 - x28) ≤ (t - 1)) ∨ ((x27 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x28) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9302 (t x27 x28 x78 : ℝ) (h : (((x27 ≤ x28) ∧ (x28 ≤ x78) ∧ ((x78 - x27) ≥ 1) ∧ ((x28 - x27) ≤ (t - 1)) ∧ ((x78 - x28) ≤ (t - 1))) ∨ ((x78 ≤ x28) ∧ (x28 ≤ x27) ∧ ((x27 - x78) ≥ 1) ∧ ((x27 - x28) ≤ (t - 1)) ∧ ((x28 - x78) ≤ (t - 1))))) : (((x78 - x28) ≤ (t - 1)) ∨ ((x28 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x28) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9303 (x04 x34 x45 : ℝ) : (((x34 + ((-1) * x45)) ≥ 1) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x34)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th729 x04 x34 x45
  exact (fun hh => u0 (hh (And.intro u2 u1))) h

theorem clause9304 (t x01 x07 x12 x13 x17 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x17)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x07)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x12) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x17)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x07)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th730 t x01 x07 x12 x13 x17 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u6 (And.intro u3 (And.intro u4 (And.intro u2 u5)))))))) h

theorem clause9305 (x04 x34 x47 : ℝ) : ((¬ ((x04 + ((-1) * x34)) ≤ 0)) ∨ ((x04 + ((-1) * x47)) ≤ (-1)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th734 x04 x34 x47
  exact (fun hh => u1 (hh (And.intro u0 u2))) h

theorem clause9306 (t x01 x04 x12 x13 x14 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x12) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th735 t x01 x04 x12 x13 x14 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u6 (And.intro u4 (And.intro u0 (And.intro u1 u3)))))))) h

theorem clause9308 (t x05 x34 x35 x45 x47 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + x45 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x45 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th741 t x05 x34 x35 x45 x47 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u5 u4)))))))) h

theorem clause9309 (t x04 x05 x34 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x04 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x04 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th742 t x04 x05 x34 x45 x56
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u2 (And.intro u1 (And.intro u4 (And.intro u0 u5)))))) h

theorem clause9310 (x05 x45 x56 : ℝ) : ((¬ ((x05 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x05 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th743 x05 x45 x56
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u2 u1))) h

theorem clause9311 (t x01 x12 x16 x26 : ℝ) : ((¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x16)) ≤ 0)) ∨ ((t + ((-1) * x12) + x16) ≥ 1) ∨ ((t + ((-1) * x26)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x12) + x16) ≥ 1) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x26)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th745 t x01 x12 x16 x26
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u3 u4))))))) h

theorem clause9312 (t x26 : ℝ) : ((¬ ((t + ((-1) * x26)) ≤ 0)) ∨ (t ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x26) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th746 t x26
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause9314 (t x26 : ℝ) : ((¬ (t ≤ x26)) ∨ (¬ (x26 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x26 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th747 t x26
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause9316 (t x26 : ℝ) (h : (x26 < t)) : ((x26 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 < t) := fun hh => hn hh
  exact u0 h

theorem clause9317 (t x01 x03 x12 x13 x35 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x12) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th749 t x01 x03 x12 x13 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u5 (And.intro u1 u4))))))) h

theorem clause9318 (t x01 x12 x13 x16 x27 x36 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x12) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x68) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th751 t x01 x12 x13 x16 x27 x36 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u6 (And.intro u3 (And.intro u8 (And.intro u4 u5)))))))))) h

theorem clause9320 (t x01 x12 x13 x23 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th755 t x01 x12 x13 x23 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u6 (And.intro u5 (And.intro u3 u4)))))))) h

theorem clause9321 (t x01 x15 x16 x35 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x16 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x56 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x15 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th756 t x01 x15 x16 x35 x56 x57
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u6 (And.intro u3 (And.intro u0 (And.intro u4 (And.intro u2 u5))))))) h

theorem clause9322 (x05 x35 x56 : ℝ) : ((¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ ((x35 + ((-1) * x56)) ≥ 1) ∨ (¬ ((x05 + ((-1) * x35)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th757 x05 x35 x56
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause9323 (t x03 x34 x35 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ (x34 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x34)) ≥ 1) := by
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
  have u4 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th760 t x03 x34 x35 x56 x67
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u2 (And.intro u5 (And.intro u0 (And.intro u6 (And.intro u3 u4))))))) h

theorem clause9324 (t x01 x12 x15 x35 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ (x35 ≥ 0)) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th761 t x01 x12 x15 x35 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u4 (And.intro u1 (And.intro u6 (And.intro u3 u5)))))))) h

theorem clause9325 (t x01 x03 x05 x12 x13 x17 x35 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + x17 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x12) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + x17 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th762 t x01 x03 x05 x12 x13 x17 x35 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u9 (And.intro u4 (And.intro u7 (And.intro u0 (And.intro u2 (And.intro u5 (And.intro u1 (And.intro u6 (And.intro u8 u3))))))))))) h

theorem clause9327 (x35 x56 x57 : ℝ) : ((¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x57)) ≥ 0)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th766 x35 x56 x57
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u2 u0))) h

theorem clause9328 (x03 x23 x34 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th769 x03 x23 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 u1)))) h

theorem clause9329 (t x01 x14 x17 x34 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x14 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x47)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x14 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x17 + ((-1) * x47)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th771 t x01 x14 x17 x34 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u5 (And.intro u1 (And.intro u2 u0))))))) h

theorem clause9330 (x14 x24 x47 : ℝ) : ((¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x24)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th773 x14 x24 x47
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u2 u0))) h

theorem clause9331 (t x03 x05 x12 x13 x24 x35 x47 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + x47 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x12) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x47 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th774 t x03 x05 x12 x13 x24 x35 x47 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u5 (And.intro u6 (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u8 (And.intro u9 (And.intro u1 u3))))))))))) h

theorem clause9332 (t x03 x34 x45 x56 x67 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ (x03 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x03 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th775 t x03 x34 x45 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u5 (And.intro u2 (And.intro u1 u6)))))))) h

theorem clause9333 (t x03 x05 x35 x56 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x05)) ≤ 0)) ∨ (¬ (x03 ≥ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th779 t x03 x05 x35 x56 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u6 (And.intro u3 (And.intro u4 (And.intro u2 (And.intro u7 u5))))))))) h

theorem clause9335 (x15 : ℝ) (h : (x15 ≥ 0)) : ((x15 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause9336 (t x03 x05 x12 x13 x17 x27 x35 x56 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + x27 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x17)) ≥ 0)) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x12) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x27 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x12 + ((-1) * x17)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x27 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th782 t x03 x05 x12 x13 x17 x27 x35 x56 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u6 (And.intro u1 (And.intro u2 (And.intro u7 (And.intro u10 (And.intro u0 (And.intro u4 (And.intro u9 u8)))))))))))) h

theorem clause9337 (x27 x57 x78 : ℝ) : ((¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x57)) ≥ 0)) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x27 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x27 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th783 x27 x57 x78
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u0 u2))) h

theorem clause9338 (t x35 x56 x57 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x67) + x68) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x57 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x67) + x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th785 t x35 x56 x57 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u5 u2))))))) h

theorem clause9339 (t x03 x23 x35 x36 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ ((t + ((-1) * x57)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th786 t x03 x23 x35 x36 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u5 (And.intro u6 (And.intro u2 u1)))))))) h

theorem clause9340 (x35 x57 : ℝ) : ((¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th787 x35 x57
  exact (fun hh => (Or.elim hh (fun hh => hh u1) (fun zz => ((fun hh => hh u0) zz)))) h

theorem clause9341 (x17 x67 x78 : ℝ) : ((¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x17 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th789 x17 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause9342 (t x35 x36 x56 x57 x68 : ℝ) : ((¬ ((x35 + ((-1) * x36)) ≥ 0)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + x56 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th790 t x35 x36 x56 x57 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u5 (And.intro u1 (And.intro u0 u3))))))) h

theorem clause9343 (t x01 x05 x12 x13 x14 x15 x34 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x14) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x15)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ (x34 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x15)) ≥ 0)) ∨ ((t + ((-1) * x57)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x12) + x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x05 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th793 t x01 x05 x12 x13 x14 x15 x34 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u11 (And.intro u5 (And.intro u1 (And.intro u3 (And.intro u0 (And.intro u8 (And.intro u2 (And.intro u10 (And.intro u6 (And.intro u4 (And.intro u7 u9))))))))))))) h

theorem clause9344 (x01 x14 : ℝ) : ((¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th795 x01 x14
  exact (fun hh => (Or.elim hh (fun hh => hh u0) (fun zz => ((fun hh => hh u1) zz)))) h

theorem clause9345 (x01 x04 x14 x15 : ℝ) : ((¬ ((x04 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x15)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th797 x01 x04 x14 x15
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u3 u1))))) h

theorem clause9346 (x01 x04 x15 x45 : ℝ) : ((¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x15 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th800 x01 x04 x15 x45
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u1 (And.intro u3 u2)))) h

theorem clause9347 (t x03 x12 x13 x24 x35 x47 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + x47 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x12) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x47 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th802 t x03 x12 x13 x24 x35 x47 x56 x67
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u7 (And.intro u3 (And.intro u2 (And.intro u8 (And.intro u1 (And.intro u5 (And.intro u0 u4))))))))) h

theorem clause9348 (t x02 x04 x05 x24 x35 x45 x47 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((t + ((-1) * x02) + x05) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ (x45 ≥ 0)) ∨ ((t + ((-1) * x57)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x02) + x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th804 t x02 x04 x05 x24 x35 x45 x47 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u10 (And.intro u8 (And.intro u0 (And.intro u6 (And.intro u7 (And.intro u9 (And.intro u3 (And.intro u2 (And.intro u5 (And.intro u1 u4)))))))))))) h

theorem clause9349 (t x01 x14 x15 x34 x45 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x14 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((t + x45 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x15 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x45 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th805 t x01 x14 x15 x34 x45 x47
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u1 (And.intro u0 (And.intro u6 (And.intro u3 (And.intro u4 u2))))))) h

theorem clause9350 (t x01 x13 x14 x34 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th806 t x01 x13 x14 x34 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u1 (And.intro u6 (And.intro u2 u5)))))))) h

theorem clause9351 (t x02 x03 x04 x24 x35 x45 x47 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x02) + x03) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ (x45 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x02) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th810 t x02 x03 x04 x24 x35 x45 x47 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u10 (And.intro u9 (And.intro u3 (And.intro u2 (And.intro u4 (And.intro u5 (And.intro u1 (And.intro u7 (And.intro u6 u8)))))))))))) h

theorem clause9352 (x14 : ℝ) (h : (x14 ≥ 0)) : ((x14 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause9353 (t x01 x03 x12 x13 x16 x36 x46 x68 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((t + x16 + ((-1) * x46)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x12) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x16 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th814 t x01 x03 x12 x13 x16 x36 x46 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u6 (And.intro u5 (And.intro u8 (And.intro u7 u0)))))))))) h

theorem clause9354 (t x01 x12 x17 x27 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1))) ∨ (¬ (x27 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x27 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th817 t x01 x12 x17 x27 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u0 (And.intro u5 (And.intro u3 (And.intro u1 (And.intro u2 u4)))))))) h

theorem clause9355 (t x01 x03 x12 x13 x14 x35 x45 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ (x45 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x12) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th818 t x01 x03 x12 x13 x14 x35 x45 x56 x67
  exact (fun hh => (fun hh => hh u9) (hh (And.intro u1 (And.intro u6 (And.intro u5 (And.intro u2 (And.intro u4 (And.intro u10 (And.intro u0 (And.intro u8 (And.intro u3 u7))))))))))) h

theorem clause9356 (x01 x12 x14 : ℝ) : ((¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x14)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th819 x01 x12 x14
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u0 u1))) h

theorem clause9357 (t x34 x46 x47 x57 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((x47 + ((-1) * x57)) ≤ 0)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x67) + x68) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x57 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x67) + x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th824 t x34 x46 x47 x57 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u3 (And.intro u6 (And.intro u5 (And.intro u0 u2)))))))) h

theorem clause9358 (t x03 x04 x07 x27 x34 x45 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + x03 + ((-1) * x07)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + x27 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x07 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x03 + ((-1) * x07)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x27 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x27 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th825 t x03 x04 x07 x27 x34 x45 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u2 (And.intro u1 (And.intro u6 (And.intro u5 (And.intro u0 (And.intro u7 u8)))))))))) h

theorem clause9360 (x34 x45 x46 : ℝ) : ((¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x46)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th830 x34 x45 x46
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u2 u0))) h

theorem clause9361 (t x01 x03 x12 x13 x15 x34 x35 x45 x57 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((t + x15 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x12) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x15 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th831 t x01 x03 x12 x13 x15 x34 x35 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u4 (And.intro u0 (And.intro u5 (And.intro u3 (And.intro u8 (And.intro u9 (And.intro u6 (And.intro u1 u2))))))))))) h

theorem clause9362 (x34 x45 x46 : ℝ) : ((¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ ((x34 + ((-1) * x45)) ≤ (-1)) ∨ (¬ ((x45 + ((-1) * x46)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th832 x34 x45 x46
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause9363 (t x03 x35 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ (x03 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ ((t + ((-1) * x57)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x03 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th833 t x03 x35 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u1 (And.intro u5 u3)))))))) h

theorem clause9364 (t x13 x14 x46 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x14)) ≤ 0)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th834 t x13 x14 x46 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u3 (And.intro u7 (And.intro u4 (And.intro u5 (And.intro u1 u6))))))))) h

theorem clause9365 (t x12 x13 x15 : ℝ) : ((¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x15)) ≤ 0)) ∨ ((t + ((-1) * x12) + x15) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x12) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x12) + x15) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th835 t x12 x13 x15
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause9366 (t x01 x03 x12 x13 x15 x35 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x12) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x56 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th836 t x01 x03 x12 x13 x15 x35 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u3 (And.intro u0 (And.intro u4 (And.intro u6 (And.intro u7 (And.intro u5 (And.intro u1 u2)))))))))) h

theorem clause9367 (x01 x15 x17 : ℝ) : (((x01 + ((-1) * x15)) ≥ 1) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x17)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x15)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x15 + ((-1) * x17)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th838 x01 x15 x17
  exact (fun hh => u0 (hh (And.intro u2 u1))) h

theorem clause9368 (x03 x35 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th839 x03 x35
  exact (fun hh => (Or.elim hh (fun hh => hh u1) (fun zz => ((fun hh => hh u0) zz)))) h

theorem clause9369 (t x01 x05 x12 x15 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x12) + x15) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x12) + x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th842 t x01 x05 x12 x15 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u4 u5))))))) h

theorem clause9370 (t x01 x13 x15 x35 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x15 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th844 t x01 x13 x15 x35 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u6 (And.intro u5 (And.intro u4 u7))))))))) h

theorem clause9371 (t x01 x15 x17 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x57)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x56 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th846 t x01 x15 x17 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u3 (And.intro u0 (And.intro u4 u1))))))) h

theorem clause9372 (t x01 x15 x17 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ ((t + ((-1) * x17)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th849 t x01 x15 x17 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u1 (And.intro u5 u6)))))))) h

theorem clause9373 (t x17 : ℝ) : ((¬ ((t + ((-1) * x17)) ≤ 0)) ∨ (t ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x17)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x17) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th850 t x17
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause9375 (t x17 : ℝ) : ((¬ (t ≤ x17)) ∨ (¬ (x17 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x17 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th851 t x17
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause9377 (t x17 : ℝ) (h : (x17 < t)) : ((x17 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 < t) := fun hh => hn hh
  exact u0 h

theorem clause9378 (x34 x35 x47 x57 : ℝ) : ((¬ ((x34 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x57)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x47 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th859 x34 x35 x47 x57
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u1 (And.intro u2 u3)))) h

theorem clause9379 (x35 x45 x57 : ℝ) : ((¬ ((x35 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th860 x35 x45 x57
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u1 u2))) h

theorem clause9380 (x01 x04 x12 x24 : ℝ) : ((¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th862 x01 x04 x12 x24
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u3 u0))))) h

theorem clause9381 (x34 x45 x47 : ℝ) : (((x34 + ((-1) * x45)) ≥ 1) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x47)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x47)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th863 x34 x45 x47
  exact (fun hh => u0 (hh (And.intro u2 u1))) h

theorem clause9382 (x04 x45 x47 : ℝ) : ((¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x47)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x47)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th865 x04 x45 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 u0)))) h

theorem clause9383 (t x01 x12 x14 x34 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ (x34 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th866 t x01 x12 x14 x34 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u6 (And.intro u3 (And.intro u4 u5)))))))) h

theorem clause9384 (t x01 x12 x13 x15 x17 x27 x45 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ ((t + x27 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x17)) ≥ 0)) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x12) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x15 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x27 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x17)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x27 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th867 t x01 x12 x13 x15 x17 x27 x45 x57 x78
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u4 (And.intro u5 (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u8 (And.intro u7 u9)))))))))) h

theorem clause9385 (x05 x35 x56 : ℝ) : ((¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x35)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th869 x05 x35 x56
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u2 u0))) h

theorem clause9386 (t x01 x12 x16 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ (x36 ≥ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th870 t x01 x12 x16 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u2 (And.intro u5 (And.intro u3 (And.intro u4 (And.intro u0 u1)))))))) h

theorem clause9387 (t x01 x12 x13 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x67 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th871 t x01 x12 x13 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u3 (And.intro u5 (And.intro u6 (And.intro u1 u0)))))))) h

theorem clause9388 (x01 x13 x16 : ℝ) : ((¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ ((x01 + ((-1) * x16)) ≥ 1) ∨ (¬ ((x13 + ((-1) * x16)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x16)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th872 x01 x13 x16
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause9390 (t x01 x02 x12 x13 x27 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x12) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x02)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th874 t x01 x02 x12 x13 x27
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u5 (And.intro u4 (And.intro u1 u2))))))) h

theorem clause9391 (t x27 : ℝ) : ((¬ ((t + ((-1) * x27)) ≤ 0)) ∨ (t ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x27)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x27) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th875 t x27
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause9393 (t x27 : ℝ) : ((¬ (t ≤ x27)) ∨ (¬ (x27 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x27 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th876 t x27
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause9395 (t x27 : ℝ) (h : (x27 < t)) : ((x27 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 < t) := fun hh => hn hh
  exact u0 h

theorem clause9396 (x01 x15 x17 : ℝ) : ((¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x17)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x15 + ((-1) * x17)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th878 x01 x15 x17
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 u0)))) h

theorem clause9397 (t x04 x05 x24 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x04) + x24) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x04) + x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th879 t x04 x05 x24 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u1 (And.intro u2 (And.intro u5 u0))))))) h

theorem clause9398 (t x02 x05 x23 x24 x25 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x23 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x24 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x23 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th880 t x02 x05 x23 x24 x25 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u5 u6)))))))) h

theorem clause9399 (t x01 x12 x13 x23 x35 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th883 t x01 x12 x13 x23 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u3 (And.intro u1 (And.intro u0 (And.intro u6 u2)))))))) h

theorem clause9400 (x25 : ℝ) (h : (x25 ≥ 0)) : ((x25 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause9401 (t x01 x04 x12 x14 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x14) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x12) + x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th887 t x01 x04 x12 x14 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u5 u3))))))) h

theorem clause9402 (t x01 x14 x15 x24 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x14) + x24) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
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
  have u4 : ((x15 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th890 t x01 x14 x15 x24 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u0 u4))))))) h

theorem clause9403 (x04 x14 x47 : ℝ) : ((¬ ((x04 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th891 x04 x14 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 u0)))) h

theorem clause9404 (t x01 x14 x15 x45 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((t + x45 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x15 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x45 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th892 t x01 x14 x15 x45 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u4 (And.intro u3 (And.intro u2 u0))))))) h

theorem clause9405 (x02 x12 : ℝ) : (((x02 + ((-1) * x12)) ≤ 0) ∨ ((x02 + ((-1) * x12)) ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x12)) ≥ 0) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th893 x02 x12
  exact (fun hh => (Or.elim hh u1 (fun zz => (u0 zz)))) h

theorem clause9406 (x24 x45 : ℝ) : ((¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th896 x24 x45
  exact (fun hh => (Or.elim hh (fun hh => hh u0) (fun zz => ((fun hh => hh u1) zz)))) h

theorem clause9407 (x02 x04 x25 x45 : ℝ) : ((¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ ((x02 + ((-1) * x25)) ≥ 1) ∨ (¬ ((x25 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x25 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th897 x02 x04 x25 x45
  exact (fun hh => u1 (hh (And.intro u3 (And.intro u2 u0)))) h

theorem clause9408 (t x02 x12 x23 x24 x25 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ (¬ (x25 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x25 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th898 t x02 x12 x23 x24 x25
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u5 (And.intro u3 (And.intro u0 (And.intro u2 u6)))))))) h

theorem clause9409 (x02 x03 x24 x34 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th902 x02 x03 x24 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u3 u1))))) h

theorem clause9410 (x24 x45 x46 : ℝ) : ((¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x46)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th904 x24 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 u1)))) h

theorem clause9411 (t x24 x45 x46 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x56 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th905 t x24 x45 x46 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u2 u5))))))) h

theorem clause9412 (x24 x47 : ℝ) : ((¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th906 x24 x47
  exact (fun hh => (Or.elim hh (fun hh => hh u0) (fun zz => ((fun hh => hh u1) zz)))) h

theorem clause9413 (x01 x17 : ℝ) : ((¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th907 x01 x17
  exact (fun hh => (Or.elim hh (fun hh => hh u1) (fun zz => ((fun hh => hh u0) zz)))) h

theorem clause9415 (t x04 x24 x27 x46 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ (x46 ≥ 0)) ∨ ((t + ((-1) * x04)) ≤ 0) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x27)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x04)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x24 + ((-1) * x27)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th910 t x04 x24 x27 x46 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u7 (And.intro u5 u6))))))))) h

theorem clause9416 (t x07 x24 x46 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x46 ≥ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ ((t + ((-1) * x07)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x07 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x46 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x07)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th911 t x07 x24 x46 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u6 (And.intro u2 (And.intro u3 (And.intro u1 (And.intro u4 u5)))))))) h

theorem clause9417 (t x07 : ℝ) : ((¬ ((t + ((-1) * x07)) ≤ 0)) ∨ (t ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x07)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x07) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th912 t x07
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause9419 (t x07 : ℝ) : ((¬ (t ≤ x07)) ∨ (¬ (x07 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x07 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th913 t x07
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause9421 (t x07 : ℝ) (h : (x07 < t)) : ((x07 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 < t) := fun hh => hn hh
  exact u0 h

theorem clause9423 (t x04 x24 x45 x46 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ ((t + ((-1) * x04)) ≤ 0) ∨ (¬ (x68 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x04)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x68 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th917 t x04 x24 x45 x46 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u1 (And.intro u3 (And.intro u0 (And.intro u6 u4)))))))) h

theorem clause9435 (t x16 x18 x68 : ℝ) : (((x16 + ((-1) * x68)) ≤ (-1)) ∨ ((x18 + ((-1) * x68)) ≥ 0) ∨ (¬ (x16 ≤ x18)) ∨ (¬ (x18 ≤ x68)) ∨ (¬ ((x68 - x16) ≥ 1)) ∨ (¬ ((x18 - x16) ≤ (t - 1))) ∨ (¬ ((x68 - x18) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 + ((-1) * x68)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x16 ≤ x18) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x18 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x18 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x18) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th920 t x16 x18 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9437 (t x16 x18 x68 : ℝ) : (((x16 + ((-1) * x68)) ≥ 1) ∨ ((x16 + ((-1) * x68)) ≤ (-1)) ∨ (¬ (x16 ≤ x18)) ∨ (¬ (x18 ≤ x68)) ∨ (¬ ((x68 - x16) ≥ 1)) ∨ (¬ ((x18 - x16) ≤ (t - 1))) ∨ (¬ ((x68 - x18) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x16 ≤ x18) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x18 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x18 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x18) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th920 t x16 x18 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9447 (t x16 x18 x68 : ℝ) : (((x16 + ((-1) * x68)) ≥ 1) ∨ ((t + x18 + ((-1) * x68)) ≥ 1) ∨ (¬ (x16 ≤ x18)) ∨ (¬ (x18 ≤ x68)) ∨ (¬ ((x68 - x16) ≥ 1)) ∨ (¬ ((x18 - x16) ≤ (t - 1))) ∨ (¬ ((x68 - x18) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x18 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x16 ≤ x18) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x18 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x18 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x18) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th920 t x16 x18 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9460 (t x16 x18 x68 : ℝ) : (((x16 + ((-1) * x68)) ≤ (-1)) ∨ ((x18 + ((-1) * x68)) ≥ 0) ∨ (¬ (x68 ≤ x18)) ∨ (¬ (x18 ≤ x16)) ∨ (¬ ((x16 - x68) ≥ 1)) ∨ (¬ ((x16 - x18) ≤ (t - 1))) ∨ (¬ ((x18 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 + ((-1) * x68)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x18) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x18 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x18) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x18 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th920 t x16 x18 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9462 (t x16 x18 x68 : ℝ) : (((x16 + ((-1) * x68)) ≥ 1) ∨ ((x16 + ((-1) * x68)) ≤ (-1)) ∨ (¬ (x68 ≤ x18)) ∨ (¬ (x18 ≤ x16)) ∨ (¬ ((x16 - x68) ≥ 1)) ∨ (¬ ((x16 - x18) ≤ (t - 1))) ∨ (¬ ((x18 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x18) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x18 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x18) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x18 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th920 t x16 x18 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9472 (t x16 x18 x68 : ℝ) : (((x16 + ((-1) * x68)) ≥ 1) ∨ ((t + x18 + ((-1) * x68)) ≥ 1) ∨ (¬ (x68 ≤ x18)) ∨ (¬ (x18 ≤ x16)) ∨ (¬ ((x16 - x68) ≥ 1)) ∨ (¬ ((x16 - x18) ≤ (t - 1))) ∨ (¬ ((x18 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x18 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x18) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x18 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x18) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x18 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th920 t x16 x18 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9525 (t x16 x18 x68 : ℝ) (h : (((x16 ≤ x18) ∧ (x18 ≤ x68) ∧ ((x68 - x16) ≥ 1) ∧ ((x18 - x16) ≤ (t - 1)) ∧ ((x68 - x18) ≤ (t - 1))) ∨ ((x68 ≤ x18) ∧ (x18 ≤ x16) ∧ ((x16 - x68) ≥ 1) ∧ ((x16 - x18) ≤ (t - 1)) ∧ ((x18 - x68) ≤ (t - 1))))) : ((x16 ≤ x18) ∨ (x68 ≤ x18)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x18) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9526 (t x16 x18 x68 : ℝ) (h : (((x16 ≤ x18) ∧ (x18 ≤ x68) ∧ ((x68 - x16) ≥ 1) ∧ ((x18 - x16) ≤ (t - 1)) ∧ ((x68 - x18) ≤ (t - 1))) ∨ ((x68 ≤ x18) ∧ (x18 ≤ x16) ∧ ((x16 - x68) ≥ 1) ∧ ((x16 - x18) ≤ (t - 1)) ∧ ((x18 - x68) ≤ (t - 1))))) : ((x16 ≤ x18) ∨ (x18 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9527 (t x16 x18 x68 : ℝ) (h : (((x16 ≤ x18) ∧ (x18 ≤ x68) ∧ ((x68 - x16) ≥ 1) ∧ ((x18 - x16) ≤ (t - 1)) ∧ ((x68 - x18) ≤ (t - 1))) ∨ ((x68 ≤ x18) ∧ (x18 ≤ x16) ∧ ((x16 - x68) ≥ 1) ∧ ((x16 - x18) ≤ (t - 1)) ∧ ((x18 - x68) ≤ (t - 1))))) : ((x16 ≤ x18) ∨ ((x16 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9528 (t x16 x18 x68 : ℝ) (h : (((x16 ≤ x18) ∧ (x18 ≤ x68) ∧ ((x68 - x16) ≥ 1) ∧ ((x18 - x16) ≤ (t - 1)) ∧ ((x68 - x18) ≤ (t - 1))) ∨ ((x68 ≤ x18) ∧ (x18 ≤ x16) ∧ ((x16 - x68) ≥ 1) ∧ ((x16 - x18) ≤ (t - 1)) ∧ ((x18 - x68) ≤ (t - 1))))) : ((x16 ≤ x18) ∨ ((x16 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9529 (t x16 x18 x68 : ℝ) (h : (((x16 ≤ x18) ∧ (x18 ≤ x68) ∧ ((x68 - x16) ≥ 1) ∧ ((x18 - x16) ≤ (t - 1)) ∧ ((x68 - x18) ≤ (t - 1))) ∨ ((x68 ≤ x18) ∧ (x18 ≤ x16) ∧ ((x16 - x68) ≥ 1) ∧ ((x16 - x18) ≤ (t - 1)) ∧ ((x18 - x68) ≤ (t - 1))))) : ((x16 ≤ x18) ∨ ((x18 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9530 (t x16 x18 x68 : ℝ) (h : (((x16 ≤ x18) ∧ (x18 ≤ x68) ∧ ((x68 - x16) ≥ 1) ∧ ((x18 - x16) ≤ (t - 1)) ∧ ((x68 - x18) ≤ (t - 1))) ∨ ((x68 ≤ x18) ∧ (x18 ≤ x16) ∧ ((x16 - x68) ≥ 1) ∧ ((x16 - x18) ≤ (t - 1)) ∧ ((x18 - x68) ≤ (t - 1))))) : ((x18 ≤ x68) ∨ (x68 ≤ x18)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x18 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x18) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9531 (t x16 x18 x68 : ℝ) (h : (((x16 ≤ x18) ∧ (x18 ≤ x68) ∧ ((x68 - x16) ≥ 1) ∧ ((x18 - x16) ≤ (t - 1)) ∧ ((x68 - x18) ≤ (t - 1))) ∨ ((x68 ≤ x18) ∧ (x18 ≤ x16) ∧ ((x16 - x68) ≥ 1) ∧ ((x16 - x18) ≤ (t - 1)) ∧ ((x18 - x68) ≤ (t - 1))))) : ((x18 ≤ x68) ∨ (x18 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x18 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9532 (t x16 x18 x68 : ℝ) (h : (((x16 ≤ x18) ∧ (x18 ≤ x68) ∧ ((x68 - x16) ≥ 1) ∧ ((x18 - x16) ≤ (t - 1)) ∧ ((x68 - x18) ≤ (t - 1))) ∨ ((x68 ≤ x18) ∧ (x18 ≤ x16) ∧ ((x16 - x68) ≥ 1) ∧ ((x16 - x18) ≤ (t - 1)) ∧ ((x18 - x68) ≤ (t - 1))))) : ((x18 ≤ x68) ∨ ((x16 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x18 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9533 (t x16 x18 x68 : ℝ) (h : (((x16 ≤ x18) ∧ (x18 ≤ x68) ∧ ((x68 - x16) ≥ 1) ∧ ((x18 - x16) ≤ (t - 1)) ∧ ((x68 - x18) ≤ (t - 1))) ∨ ((x68 ≤ x18) ∧ (x18 ≤ x16) ∧ ((x16 - x68) ≥ 1) ∧ ((x16 - x18) ≤ (t - 1)) ∧ ((x18 - x68) ≤ (t - 1))))) : ((x18 ≤ x68) ∨ ((x16 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x18 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9534 (t x16 x18 x68 : ℝ) (h : (((x16 ≤ x18) ∧ (x18 ≤ x68) ∧ ((x68 - x16) ≥ 1) ∧ ((x18 - x16) ≤ (t - 1)) ∧ ((x68 - x18) ≤ (t - 1))) ∨ ((x68 ≤ x18) ∧ (x18 ≤ x16) ∧ ((x16 - x68) ≥ 1) ∧ ((x16 - x18) ≤ (t - 1)) ∧ ((x18 - x68) ≤ (t - 1))))) : ((x18 ≤ x68) ∨ ((x18 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x18 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9535 (t x16 x18 x68 : ℝ) (h : (((x16 ≤ x18) ∧ (x18 ≤ x68) ∧ ((x68 - x16) ≥ 1) ∧ ((x18 - x16) ≤ (t - 1)) ∧ ((x68 - x18) ≤ (t - 1))) ∨ ((x68 ≤ x18) ∧ (x18 ≤ x16) ∧ ((x16 - x68) ≥ 1) ∧ ((x16 - x18) ≤ (t - 1)) ∧ ((x18 - x68) ≤ (t - 1))))) : (((x68 - x16) ≥ 1) ∨ (x68 ≤ x18)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x16) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x18) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9536 (t x16 x18 x68 : ℝ) (h : (((x16 ≤ x18) ∧ (x18 ≤ x68) ∧ ((x68 - x16) ≥ 1) ∧ ((x18 - x16) ≤ (t - 1)) ∧ ((x68 - x18) ≤ (t - 1))) ∨ ((x68 ≤ x18) ∧ (x18 ≤ x16) ∧ ((x16 - x68) ≥ 1) ∧ ((x16 - x18) ≤ (t - 1)) ∧ ((x18 - x68) ≤ (t - 1))))) : (((x68 - x16) ≥ 1) ∨ (x18 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x16) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9537 (t x16 x18 x68 : ℝ) (h : (((x16 ≤ x18) ∧ (x18 ≤ x68) ∧ ((x68 - x16) ≥ 1) ∧ ((x18 - x16) ≤ (t - 1)) ∧ ((x68 - x18) ≤ (t - 1))) ∨ ((x68 ≤ x18) ∧ (x18 ≤ x16) ∧ ((x16 - x68) ≥ 1) ∧ ((x16 - x18) ≤ (t - 1)) ∧ ((x18 - x68) ≤ (t - 1))))) : (((x68 - x16) ≥ 1) ∨ ((x16 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x16) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9538 (t x16 x18 x68 : ℝ) (h : (((x16 ≤ x18) ∧ (x18 ≤ x68) ∧ ((x68 - x16) ≥ 1) ∧ ((x18 - x16) ≤ (t - 1)) ∧ ((x68 - x18) ≤ (t - 1))) ∨ ((x68 ≤ x18) ∧ (x18 ≤ x16) ∧ ((x16 - x68) ≥ 1) ∧ ((x16 - x18) ≤ (t - 1)) ∧ ((x18 - x68) ≤ (t - 1))))) : (((x68 - x16) ≥ 1) ∨ ((x16 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x16) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9539 (t x16 x18 x68 : ℝ) (h : (((x16 ≤ x18) ∧ (x18 ≤ x68) ∧ ((x68 - x16) ≥ 1) ∧ ((x18 - x16) ≤ (t - 1)) ∧ ((x68 - x18) ≤ (t - 1))) ∨ ((x68 ≤ x18) ∧ (x18 ≤ x16) ∧ ((x16 - x68) ≥ 1) ∧ ((x16 - x18) ≤ (t - 1)) ∧ ((x18 - x68) ≤ (t - 1))))) : (((x68 - x16) ≥ 1) ∨ ((x18 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x16) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9540 (t x16 x18 x68 : ℝ) (h : (((x16 ≤ x18) ∧ (x18 ≤ x68) ∧ ((x68 - x16) ≥ 1) ∧ ((x18 - x16) ≤ (t - 1)) ∧ ((x68 - x18) ≤ (t - 1))) ∨ ((x68 ≤ x18) ∧ (x18 ≤ x16) ∧ ((x16 - x68) ≥ 1) ∧ ((x16 - x18) ≤ (t - 1)) ∧ ((x18 - x68) ≤ (t - 1))))) : (((x18 - x16) ≤ (t - 1)) ∨ (x68 ≤ x18)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x18) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9541 (t x16 x18 x68 : ℝ) (h : (((x16 ≤ x18) ∧ (x18 ≤ x68) ∧ ((x68 - x16) ≥ 1) ∧ ((x18 - x16) ≤ (t - 1)) ∧ ((x68 - x18) ≤ (t - 1))) ∨ ((x68 ≤ x18) ∧ (x18 ≤ x16) ∧ ((x16 - x68) ≥ 1) ∧ ((x16 - x18) ≤ (t - 1)) ∧ ((x18 - x68) ≤ (t - 1))))) : (((x18 - x16) ≤ (t - 1)) ∨ (x18 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9542 (t x16 x18 x68 : ℝ) (h : (((x16 ≤ x18) ∧ (x18 ≤ x68) ∧ ((x68 - x16) ≥ 1) ∧ ((x18 - x16) ≤ (t - 1)) ∧ ((x68 - x18) ≤ (t - 1))) ∨ ((x68 ≤ x18) ∧ (x18 ≤ x16) ∧ ((x16 - x68) ≥ 1) ∧ ((x16 - x18) ≤ (t - 1)) ∧ ((x18 - x68) ≤ (t - 1))))) : (((x18 - x16) ≤ (t - 1)) ∨ ((x16 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9543 (t x16 x18 x68 : ℝ) (h : (((x16 ≤ x18) ∧ (x18 ≤ x68) ∧ ((x68 - x16) ≥ 1) ∧ ((x18 - x16) ≤ (t - 1)) ∧ ((x68 - x18) ≤ (t - 1))) ∨ ((x68 ≤ x18) ∧ (x18 ≤ x16) ∧ ((x16 - x68) ≥ 1) ∧ ((x16 - x18) ≤ (t - 1)) ∧ ((x18 - x68) ≤ (t - 1))))) : (((x18 - x16) ≤ (t - 1)) ∨ ((x16 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9544 (t x16 x18 x68 : ℝ) (h : (((x16 ≤ x18) ∧ (x18 ≤ x68) ∧ ((x68 - x16) ≥ 1) ∧ ((x18 - x16) ≤ (t - 1)) ∧ ((x68 - x18) ≤ (t - 1))) ∨ ((x68 ≤ x18) ∧ (x18 ≤ x16) ∧ ((x16 - x68) ≥ 1) ∧ ((x16 - x18) ≤ (t - 1)) ∧ ((x18 - x68) ≤ (t - 1))))) : (((x18 - x16) ≤ (t - 1)) ∨ ((x18 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9545 (t x16 x18 x68 : ℝ) (h : (((x16 ≤ x18) ∧ (x18 ≤ x68) ∧ ((x68 - x16) ≥ 1) ∧ ((x18 - x16) ≤ (t - 1)) ∧ ((x68 - x18) ≤ (t - 1))) ∨ ((x68 ≤ x18) ∧ (x18 ≤ x16) ∧ ((x16 - x68) ≥ 1) ∧ ((x16 - x18) ≤ (t - 1)) ∧ ((x18 - x68) ≤ (t - 1))))) : (((x68 - x18) ≤ (t - 1)) ∨ (x68 ≤ x18)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x18) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x18) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9546 (t x16 x18 x68 : ℝ) (h : (((x16 ≤ x18) ∧ (x18 ≤ x68) ∧ ((x68 - x16) ≥ 1) ∧ ((x18 - x16) ≤ (t - 1)) ∧ ((x68 - x18) ≤ (t - 1))) ∨ ((x68 ≤ x18) ∧ (x18 ≤ x16) ∧ ((x16 - x68) ≥ 1) ∧ ((x16 - x18) ≤ (t - 1)) ∧ ((x18 - x68) ≤ (t - 1))))) : (((x68 - x18) ≤ (t - 1)) ∨ (x18 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x18) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9547 (t x16 x18 x68 : ℝ) (h : (((x16 ≤ x18) ∧ (x18 ≤ x68) ∧ ((x68 - x16) ≥ 1) ∧ ((x18 - x16) ≤ (t - 1)) ∧ ((x68 - x18) ≤ (t - 1))) ∨ ((x68 ≤ x18) ∧ (x18 ≤ x16) ∧ ((x16 - x68) ≥ 1) ∧ ((x16 - x18) ≤ (t - 1)) ∧ ((x18 - x68) ≤ (t - 1))))) : (((x68 - x18) ≤ (t - 1)) ∨ ((x16 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x18) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9548 (t x16 x18 x68 : ℝ) (h : (((x16 ≤ x18) ∧ (x18 ≤ x68) ∧ ((x68 - x16) ≥ 1) ∧ ((x18 - x16) ≤ (t - 1)) ∧ ((x68 - x18) ≤ (t - 1))) ∨ ((x68 ≤ x18) ∧ (x18 ≤ x16) ∧ ((x16 - x68) ≥ 1) ∧ ((x16 - x18) ≤ (t - 1)) ∧ ((x18 - x68) ≤ (t - 1))))) : (((x68 - x18) ≤ (t - 1)) ∨ ((x16 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x18) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9549 (t x16 x18 x68 : ℝ) (h : (((x16 ≤ x18) ∧ (x18 ≤ x68) ∧ ((x68 - x16) ≥ 1) ∧ ((x18 - x16) ≤ (t - 1)) ∧ ((x68 - x18) ≤ (t - 1))) ∨ ((x68 ≤ x18) ∧ (x18 ≤ x16) ∧ ((x16 - x68) ≥ 1) ∧ ((x16 - x18) ≤ (t - 1)) ∧ ((x18 - x68) ≤ (t - 1))))) : (((x68 - x18) ≤ (t - 1)) ∨ ((x18 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x18) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

#print axioms clause9549
end NineCNFDirectTrial
