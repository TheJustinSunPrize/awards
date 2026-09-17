import NineTheoryTrial

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineCNFDirectTrial

theorem clause1 (x03 x35 x36 : ℝ) : ((¬ ((x35 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th0 x03 x35 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause2 (t x01 x03 x05 x34 x46 x56 : ℝ) : ((¬ ((x46 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x46 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1 t x01 x03 x05 x34 x46 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6)))))))) h

theorem clause4 (x13 x34 : ℝ) : ((¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th3 x13 x34
  exact (fun hh => (Or.elim hh (fun hh => hh u0) (fun zz => ((fun hh => hh u1) zz)))) h

theorem clause7 (t x13 x14 x34 : ℝ) : (((x13 + ((-1) * x34)) ≥ 1) ∨ ((x13 + ((-1) * x14)) ≤ 0) ∨ (¬ (x13 ≤ x14)) ∨ (¬ (x14 ≤ x34)) ∨ (¬ ((x34 - x13) ≥ 1)) ∨ (¬ ((x14 - x13) ≤ (t - 1))) ∨ (¬ ((x34 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x14)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5 t x13 x14 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8 (t x13 x14 x34 : ℝ) : (((x13 + ((-1) * x14)) ≤ 0) ∨ ((t + ((-1) * x13) + x14) ≥ 1) ∨ (¬ (x13 ≤ x14)) ∨ (¬ (x14 ≤ x34)) ∨ (¬ ((x34 - x13) ≥ 1)) ∨ (¬ ((x14 - x13) ≤ (t - 1))) ∨ (¬ ((x34 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x14)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x13) + x14) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5 t x13 x14 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause11 (t x13 x14 x34 : ℝ) : (((x14 + ((-1) * x34)) ≤ 0) ∨ ((x13 + ((-1) * x14)) ≥ 0) ∨ (¬ (x13 ≤ x14)) ∨ (¬ (x14 ≤ x34)) ∨ (¬ ((x34 - x13) ≥ 1)) ∨ (¬ ((x14 - x13) ≤ (t - 1))) ∨ (¬ ((x34 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x14)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5 t x13 x14 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause12 (t x13 x14 x34 : ℝ) : (((x13 + ((-1) * x34)) ≥ 1) ∨ ((x14 + ((-1) * x34)) ≤ 0) ∨ (¬ (x13 ≤ x14)) ∨ (¬ (x14 ≤ x34)) ∨ (¬ ((x34 - x13) ≥ 1)) ∨ (¬ ((x14 - x13) ≤ (t - 1))) ∨ (¬ ((x34 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5 t x13 x14 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause15 (t x13 x14 x34 : ℝ) : (((x13 + ((-1) * x34)) ≤ (-1)) ∨ ((x14 + ((-1) * x34)) ≥ 0) ∨ (¬ (x13 ≤ x14)) ∨ (¬ (x14 ≤ x34)) ∨ (¬ ((x34 - x13) ≥ 1)) ∨ (¬ ((x14 - x13) ≤ (t - 1))) ∨ (¬ ((x34 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x34)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5 t x13 x14 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause16 (t x13 x14 x34 : ℝ) : (((x13 + ((-1) * x34)) ≤ (-1)) ∨ ((x13 + ((-1) * x14)) ≥ 0) ∨ (¬ (x13 ≤ x14)) ∨ (¬ (x14 ≤ x34)) ∨ (¬ ((x34 - x13) ≥ 1)) ∨ (¬ ((x14 - x13) ≤ (t - 1))) ∨ (¬ ((x34 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x14)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5 t x13 x14 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause17 (t x13 x14 x34 : ℝ) : (((x13 + ((-1) * x34)) ≤ (-1)) ∨ ((x13 + ((-1) * x34)) ≥ 1) ∨ (¬ (x13 ≤ x14)) ∨ (¬ (x14 ≤ x34)) ∨ (¬ ((x34 - x13) ≥ 1)) ∨ (¬ ((x14 - x13) ≤ (t - 1))) ∨ (¬ ((x34 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5 t x13 x14 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause18 (t x13 x14 x34 : ℝ) : (((x13 + ((-1) * x34)) ≤ (-1)) ∨ ((t + ((-1) * x13) + x14) ≥ 1) ∨ (¬ (x13 ≤ x14)) ∨ (¬ (x14 ≤ x34)) ∨ (¬ ((x34 - x13) ≥ 1)) ∨ (¬ ((x14 - x13) ≤ (t - 1))) ∨ (¬ ((x34 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x13) + x14) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5 t x13 x14 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause19 (t x13 x14 x34 : ℝ) : (((x13 + ((-1) * x34)) ≤ (-1)) ∨ ((t + ((-1) * x14) + x34) ≥ 1) ∨ (¬ (x13 ≤ x14)) ∨ (¬ (x14 ≤ x34)) ∨ (¬ ((x34 - x13) ≥ 1)) ∨ (¬ ((x14 - x13) ≤ (t - 1))) ∨ (¬ ((x34 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x14) + x34) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5 t x13 x14 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause22 (t x13 x14 x34 : ℝ) : (((x13 + ((-1) * x34)) ≥ 1) ∨ ((t + x13 + ((-1) * x14)) ≥ 1) ∨ (¬ (x13 ≤ x14)) ∨ (¬ (x14 ≤ x34)) ∨ (¬ ((x34 - x13) ≥ 1)) ∨ (¬ ((x14 - x13) ≤ (t - 1))) ∨ (¬ ((x34 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x13 + ((-1) * x14)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5 t x13 x14 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause27 (t x13 x14 x34 : ℝ) : (((x13 + ((-1) * x34)) ≥ 1) ∨ ((t + x14 + ((-1) * x34)) ≥ 1) ∨ (¬ (x13 ≤ x14)) ∨ (¬ (x14 ≤ x34)) ∨ (¬ ((x34 - x13) ≥ 1)) ∨ (¬ ((x14 - x13) ≤ (t - 1))) ∨ (¬ ((x34 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x14 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5 t x13 x14 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause32 (t x13 x14 x34 : ℝ) : (((x13 + ((-1) * x34)) ≥ 1) ∨ ((x13 + ((-1) * x14)) ≤ 0) ∨ (¬ (x34 ≤ x14)) ∨ (¬ (x14 ≤ x13)) ∨ (¬ ((x13 - x34) ≥ 1)) ∨ (¬ ((x13 - x14) ≤ (t - 1))) ∨ (¬ ((x14 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x14)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5 t x13 x14 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause36 (t x13 x14 x34 : ℝ) : (((x14 + ((-1) * x34)) ≤ 0) ∨ ((x13 + ((-1) * x14)) ≥ 0) ∨ (¬ (x34 ≤ x14)) ∨ (¬ (x14 ≤ x13)) ∨ (¬ ((x13 - x34) ≥ 1)) ∨ (¬ ((x13 - x14) ≤ (t - 1))) ∨ (¬ ((x14 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x14)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5 t x13 x14 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause37 (t x13 x14 x34 : ℝ) : (((x13 + ((-1) * x34)) ≥ 1) ∨ ((x14 + ((-1) * x34)) ≤ 0) ∨ (¬ (x34 ≤ x14)) ∨ (¬ (x14 ≤ x13)) ∨ (¬ ((x13 - x34) ≥ 1)) ∨ (¬ ((x13 - x14) ≤ (t - 1))) ∨ (¬ ((x14 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5 t x13 x14 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause40 (t x13 x14 x34 : ℝ) : (((x13 + ((-1) * x34)) ≤ (-1)) ∨ ((x14 + ((-1) * x34)) ≥ 0) ∨ (¬ (x34 ≤ x14)) ∨ (¬ (x14 ≤ x13)) ∨ (¬ ((x13 - x34) ≥ 1)) ∨ (¬ ((x13 - x14) ≤ (t - 1))) ∨ (¬ ((x14 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x34)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5 t x13 x14 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause41 (t x13 x14 x34 : ℝ) : (((x13 + ((-1) * x34)) ≤ (-1)) ∨ ((x13 + ((-1) * x14)) ≥ 0) ∨ (¬ (x34 ≤ x14)) ∨ (¬ (x14 ≤ x13)) ∨ (¬ ((x13 - x34) ≥ 1)) ∨ (¬ ((x13 - x14) ≤ (t - 1))) ∨ (¬ ((x14 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x14)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5 t x13 x14 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause42 (t x13 x14 x34 : ℝ) : (((x13 + ((-1) * x34)) ≤ (-1)) ∨ ((x13 + ((-1) * x34)) ≥ 1) ∨ (¬ (x34 ≤ x14)) ∨ (¬ (x14 ≤ x13)) ∨ (¬ ((x13 - x34) ≥ 1)) ∨ (¬ ((x13 - x14) ≤ (t - 1))) ∨ (¬ ((x14 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5 t x13 x14 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause43 (t x13 x14 x34 : ℝ) : (((x13 + ((-1) * x34)) ≤ (-1)) ∨ ((t + ((-1) * x13) + x14) ≥ 1) ∨ (¬ (x34 ≤ x14)) ∨ (¬ (x14 ≤ x13)) ∨ (¬ ((x13 - x34) ≥ 1)) ∨ (¬ ((x13 - x14) ≤ (t - 1))) ∨ (¬ ((x14 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x13) + x14) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5 t x13 x14 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause44 (t x13 x14 x34 : ℝ) : (((x13 + ((-1) * x34)) ≤ (-1)) ∨ ((t + ((-1) * x14) + x34) ≥ 1) ∨ (¬ (x34 ≤ x14)) ∨ (¬ (x14 ≤ x13)) ∨ (¬ ((x13 - x34) ≥ 1)) ∨ (¬ ((x13 - x14) ≤ (t - 1))) ∨ (¬ ((x14 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x14) + x34) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5 t x13 x14 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause47 (t x13 x14 x34 : ℝ) : (((x13 + ((-1) * x34)) ≥ 1) ∨ ((t + x13 + ((-1) * x14)) ≥ 1) ∨ (¬ (x34 ≤ x14)) ∨ (¬ (x14 ≤ x13)) ∨ (¬ ((x13 - x34) ≥ 1)) ∨ (¬ ((x13 - x14) ≤ (t - 1))) ∨ (¬ ((x14 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x13 + ((-1) * x14)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5 t x13 x14 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause52 (t x13 x14 x34 : ℝ) : (((x13 + ((-1) * x34)) ≥ 1) ∨ ((t + x14 + ((-1) * x34)) ≥ 1) ∨ (¬ (x34 ≤ x14)) ∨ (¬ (x14 ≤ x13)) ∨ (¬ ((x13 - x34) ≥ 1)) ∨ (¬ ((x13 - x14) ≤ (t - 1))) ∨ (¬ ((x14 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x14 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5 t x13 x14 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause105 (t x13 x14 x34 : ℝ) (h : (((x13 ≤ x14) ∧ (x14 ≤ x34) ∧ ((x34 - x13) ≥ 1) ∧ ((x14 - x13) ≤ (t - 1)) ∧ ((x34 - x14) ≤ (t - 1))) ∨ ((x34 ≤ x14) ∧ (x14 ≤ x13) ∧ ((x13 - x34) ≥ 1) ∧ ((x13 - x14) ≤ (t - 1)) ∧ ((x14 - x34) ≤ (t - 1))))) : ((x13 ≤ x14) ∨ (x34 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x14) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x34 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause106 (t x13 x14 x34 : ℝ) (h : (((x13 ≤ x14) ∧ (x14 ≤ x34) ∧ ((x34 - x13) ≥ 1) ∧ ((x14 - x13) ≤ (t - 1)) ∧ ((x34 - x14) ≤ (t - 1))) ∨ ((x34 ≤ x14) ∧ (x14 ≤ x13) ∧ ((x13 - x34) ≥ 1) ∧ ((x13 - x14) ≤ (t - 1)) ∧ ((x14 - x34) ≤ (t - 1))))) : ((x13 ≤ x14) ∨ (x14 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x14) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x14 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause107 (t x13 x14 x34 : ℝ) (h : (((x13 ≤ x14) ∧ (x14 ≤ x34) ∧ ((x34 - x13) ≥ 1) ∧ ((x14 - x13) ≤ (t - 1)) ∧ ((x34 - x14) ≤ (t - 1))) ∨ ((x34 ≤ x14) ∧ (x14 ≤ x13) ∧ ((x13 - x34) ≥ 1) ∧ ((x13 - x14) ≤ (t - 1)) ∧ ((x14 - x34) ≤ (t - 1))))) : ((x13 ≤ x14) ∨ ((x13 - x34) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x14) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x34) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause108 (t x13 x14 x34 : ℝ) (h : (((x13 ≤ x14) ∧ (x14 ≤ x34) ∧ ((x34 - x13) ≥ 1) ∧ ((x14 - x13) ≤ (t - 1)) ∧ ((x34 - x14) ≤ (t - 1))) ∨ ((x34 ≤ x14) ∧ (x14 ≤ x13) ∧ ((x13 - x34) ≥ 1) ∧ ((x13 - x14) ≤ (t - 1)) ∧ ((x14 - x34) ≤ (t - 1))))) : ((x13 ≤ x14) ∨ ((x13 - x14) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x14) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x14) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause109 (t x13 x14 x34 : ℝ) (h : (((x13 ≤ x14) ∧ (x14 ≤ x34) ∧ ((x34 - x13) ≥ 1) ∧ ((x14 - x13) ≤ (t - 1)) ∧ ((x34 - x14) ≤ (t - 1))) ∨ ((x34 ≤ x14) ∧ (x14 ≤ x13) ∧ ((x13 - x34) ≥ 1) ∧ ((x13 - x14) ≤ (t - 1)) ∧ ((x14 - x34) ≤ (t - 1))))) : ((x13 ≤ x14) ∨ ((x14 - x34) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x14) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x34) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause110 (t x13 x14 x34 : ℝ) (h : (((x13 ≤ x14) ∧ (x14 ≤ x34) ∧ ((x34 - x13) ≥ 1) ∧ ((x14 - x13) ≤ (t - 1)) ∧ ((x34 - x14) ≤ (t - 1))) ∨ ((x34 ≤ x14) ∧ (x14 ≤ x13) ∧ ((x13 - x34) ≥ 1) ∧ ((x13 - x14) ≤ (t - 1)) ∧ ((x14 - x34) ≤ (t - 1))))) : ((x14 ≤ x34) ∨ (x34 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x34) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x34 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause111 (t x13 x14 x34 : ℝ) (h : (((x13 ≤ x14) ∧ (x14 ≤ x34) ∧ ((x34 - x13) ≥ 1) ∧ ((x14 - x13) ≤ (t - 1)) ∧ ((x34 - x14) ≤ (t - 1))) ∨ ((x34 ≤ x14) ∧ (x14 ≤ x13) ∧ ((x13 - x34) ≥ 1) ∧ ((x13 - x14) ≤ (t - 1)) ∧ ((x14 - x34) ≤ (t - 1))))) : ((x14 ≤ x34) ∨ (x14 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x34) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x14 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause112 (t x13 x14 x34 : ℝ) (h : (((x13 ≤ x14) ∧ (x14 ≤ x34) ∧ ((x34 - x13) ≥ 1) ∧ ((x14 - x13) ≤ (t - 1)) ∧ ((x34 - x14) ≤ (t - 1))) ∨ ((x34 ≤ x14) ∧ (x14 ≤ x13) ∧ ((x13 - x34) ≥ 1) ∧ ((x13 - x14) ≤ (t - 1)) ∧ ((x14 - x34) ≤ (t - 1))))) : ((x14 ≤ x34) ∨ ((x13 - x34) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x34) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x34) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause113 (t x13 x14 x34 : ℝ) (h : (((x13 ≤ x14) ∧ (x14 ≤ x34) ∧ ((x34 - x13) ≥ 1) ∧ ((x14 - x13) ≤ (t - 1)) ∧ ((x34 - x14) ≤ (t - 1))) ∨ ((x34 ≤ x14) ∧ (x14 ≤ x13) ∧ ((x13 - x34) ≥ 1) ∧ ((x13 - x14) ≤ (t - 1)) ∧ ((x14 - x34) ≤ (t - 1))))) : ((x14 ≤ x34) ∨ ((x13 - x14) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x34) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x14) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause114 (t x13 x14 x34 : ℝ) (h : (((x13 ≤ x14) ∧ (x14 ≤ x34) ∧ ((x34 - x13) ≥ 1) ∧ ((x14 - x13) ≤ (t - 1)) ∧ ((x34 - x14) ≤ (t - 1))) ∨ ((x34 ≤ x14) ∧ (x14 ≤ x13) ∧ ((x13 - x34) ≥ 1) ∧ ((x13 - x14) ≤ (t - 1)) ∧ ((x14 - x34) ≤ (t - 1))))) : ((x14 ≤ x34) ∨ ((x14 - x34) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x34) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x34) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause115 (t x13 x14 x34 : ℝ) (h : (((x13 ≤ x14) ∧ (x14 ≤ x34) ∧ ((x34 - x13) ≥ 1) ∧ ((x14 - x13) ≤ (t - 1)) ∧ ((x34 - x14) ≤ (t - 1))) ∨ ((x34 ≤ x14) ∧ (x14 ≤ x13) ∧ ((x13 - x34) ≥ 1) ∧ ((x13 - x14) ≤ (t - 1)) ∧ ((x14 - x34) ≤ (t - 1))))) : (((x34 - x13) ≥ 1) ∨ (x34 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x13) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x34 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause116 (t x13 x14 x34 : ℝ) (h : (((x13 ≤ x14) ∧ (x14 ≤ x34) ∧ ((x34 - x13) ≥ 1) ∧ ((x14 - x13) ≤ (t - 1)) ∧ ((x34 - x14) ≤ (t - 1))) ∨ ((x34 ≤ x14) ∧ (x14 ≤ x13) ∧ ((x13 - x34) ≥ 1) ∧ ((x13 - x14) ≤ (t - 1)) ∧ ((x14 - x34) ≤ (t - 1))))) : (((x34 - x13) ≥ 1) ∨ (x14 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x13) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x14 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause117 (t x13 x14 x34 : ℝ) (h : (((x13 ≤ x14) ∧ (x14 ≤ x34) ∧ ((x34 - x13) ≥ 1) ∧ ((x14 - x13) ≤ (t - 1)) ∧ ((x34 - x14) ≤ (t - 1))) ∨ ((x34 ≤ x14) ∧ (x14 ≤ x13) ∧ ((x13 - x34) ≥ 1) ∧ ((x13 - x14) ≤ (t - 1)) ∧ ((x14 - x34) ≤ (t - 1))))) : (((x34 - x13) ≥ 1) ∨ ((x13 - x34) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x13) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x34) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause118 (t x13 x14 x34 : ℝ) (h : (((x13 ≤ x14) ∧ (x14 ≤ x34) ∧ ((x34 - x13) ≥ 1) ∧ ((x14 - x13) ≤ (t - 1)) ∧ ((x34 - x14) ≤ (t - 1))) ∨ ((x34 ≤ x14) ∧ (x14 ≤ x13) ∧ ((x13 - x34) ≥ 1) ∧ ((x13 - x14) ≤ (t - 1)) ∧ ((x14 - x34) ≤ (t - 1))))) : (((x34 - x13) ≥ 1) ∨ ((x13 - x14) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x13) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x14) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause119 (t x13 x14 x34 : ℝ) (h : (((x13 ≤ x14) ∧ (x14 ≤ x34) ∧ ((x34 - x13) ≥ 1) ∧ ((x14 - x13) ≤ (t - 1)) ∧ ((x34 - x14) ≤ (t - 1))) ∨ ((x34 ≤ x14) ∧ (x14 ≤ x13) ∧ ((x13 - x34) ≥ 1) ∧ ((x13 - x14) ≤ (t - 1)) ∧ ((x14 - x34) ≤ (t - 1))))) : (((x34 - x13) ≥ 1) ∨ ((x14 - x34) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x13) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x34) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause120 (t x13 x14 x34 : ℝ) (h : (((x13 ≤ x14) ∧ (x14 ≤ x34) ∧ ((x34 - x13) ≥ 1) ∧ ((x14 - x13) ≤ (t - 1)) ∧ ((x34 - x14) ≤ (t - 1))) ∨ ((x34 ≤ x14) ∧ (x14 ≤ x13) ∧ ((x13 - x34) ≥ 1) ∧ ((x13 - x14) ≤ (t - 1)) ∧ ((x14 - x34) ≤ (t - 1))))) : (((x14 - x13) ≤ (t - 1)) ∨ (x34 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x34 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause121 (t x13 x14 x34 : ℝ) (h : (((x13 ≤ x14) ∧ (x14 ≤ x34) ∧ ((x34 - x13) ≥ 1) ∧ ((x14 - x13) ≤ (t - 1)) ∧ ((x34 - x14) ≤ (t - 1))) ∨ ((x34 ≤ x14) ∧ (x14 ≤ x13) ∧ ((x13 - x34) ≥ 1) ∧ ((x13 - x14) ≤ (t - 1)) ∧ ((x14 - x34) ≤ (t - 1))))) : (((x14 - x13) ≤ (t - 1)) ∨ (x14 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x14 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause122 (t x13 x14 x34 : ℝ) (h : (((x13 ≤ x14) ∧ (x14 ≤ x34) ∧ ((x34 - x13) ≥ 1) ∧ ((x14 - x13) ≤ (t - 1)) ∧ ((x34 - x14) ≤ (t - 1))) ∨ ((x34 ≤ x14) ∧ (x14 ≤ x13) ∧ ((x13 - x34) ≥ 1) ∧ ((x13 - x14) ≤ (t - 1)) ∧ ((x14 - x34) ≤ (t - 1))))) : (((x14 - x13) ≤ (t - 1)) ∨ ((x13 - x34) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x34) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause123 (t x13 x14 x34 : ℝ) (h : (((x13 ≤ x14) ∧ (x14 ≤ x34) ∧ ((x34 - x13) ≥ 1) ∧ ((x14 - x13) ≤ (t - 1)) ∧ ((x34 - x14) ≤ (t - 1))) ∨ ((x34 ≤ x14) ∧ (x14 ≤ x13) ∧ ((x13 - x34) ≥ 1) ∧ ((x13 - x14) ≤ (t - 1)) ∧ ((x14 - x34) ≤ (t - 1))))) : (((x14 - x13) ≤ (t - 1)) ∨ ((x13 - x14) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x14) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause124 (t x13 x14 x34 : ℝ) (h : (((x13 ≤ x14) ∧ (x14 ≤ x34) ∧ ((x34 - x13) ≥ 1) ∧ ((x14 - x13) ≤ (t - 1)) ∧ ((x34 - x14) ≤ (t - 1))) ∨ ((x34 ≤ x14) ∧ (x14 ≤ x13) ∧ ((x13 - x34) ≥ 1) ∧ ((x13 - x14) ≤ (t - 1)) ∧ ((x14 - x34) ≤ (t - 1))))) : (((x14 - x13) ≤ (t - 1)) ∨ ((x14 - x34) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x34) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause125 (t x13 x14 x34 : ℝ) (h : (((x13 ≤ x14) ∧ (x14 ≤ x34) ∧ ((x34 - x13) ≥ 1) ∧ ((x14 - x13) ≤ (t - 1)) ∧ ((x34 - x14) ≤ (t - 1))) ∨ ((x34 ≤ x14) ∧ (x14 ≤ x13) ∧ ((x13 - x34) ≥ 1) ∧ ((x13 - x14) ≤ (t - 1)) ∧ ((x14 - x34) ≤ (t - 1))))) : (((x34 - x14) ≤ (t - 1)) ∨ (x34 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x34 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause126 (t x13 x14 x34 : ℝ) (h : (((x13 ≤ x14) ∧ (x14 ≤ x34) ∧ ((x34 - x13) ≥ 1) ∧ ((x14 - x13) ≤ (t - 1)) ∧ ((x34 - x14) ≤ (t - 1))) ∨ ((x34 ≤ x14) ∧ (x14 ≤ x13) ∧ ((x13 - x34) ≥ 1) ∧ ((x13 - x14) ≤ (t - 1)) ∧ ((x14 - x34) ≤ (t - 1))))) : (((x34 - x14) ≤ (t - 1)) ∨ (x14 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x14 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause127 (t x13 x14 x34 : ℝ) (h : (((x13 ≤ x14) ∧ (x14 ≤ x34) ∧ ((x34 - x13) ≥ 1) ∧ ((x14 - x13) ≤ (t - 1)) ∧ ((x34 - x14) ≤ (t - 1))) ∨ ((x34 ≤ x14) ∧ (x14 ≤ x13) ∧ ((x13 - x34) ≥ 1) ∧ ((x13 - x14) ≤ (t - 1)) ∧ ((x14 - x34) ≤ (t - 1))))) : (((x34 - x14) ≤ (t - 1)) ∨ ((x13 - x34) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x34) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause128 (t x13 x14 x34 : ℝ) (h : (((x13 ≤ x14) ∧ (x14 ≤ x34) ∧ ((x34 - x13) ≥ 1) ∧ ((x14 - x13) ≤ (t - 1)) ∧ ((x34 - x14) ≤ (t - 1))) ∨ ((x34 ≤ x14) ∧ (x14 ≤ x13) ∧ ((x13 - x34) ≥ 1) ∧ ((x13 - x14) ≤ (t - 1)) ∧ ((x14 - x34) ≤ (t - 1))))) : (((x34 - x14) ≤ (t - 1)) ∨ ((x13 - x14) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x14) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause129 (t x13 x14 x34 : ℝ) (h : (((x13 ≤ x14) ∧ (x14 ≤ x34) ∧ ((x34 - x13) ≥ 1) ∧ ((x14 - x13) ≤ (t - 1)) ∧ ((x34 - x14) ≤ (t - 1))) ∨ ((x34 ≤ x14) ∧ (x14 ≤ x13) ∧ ((x13 - x34) ≥ 1) ∧ ((x13 - x14) ≤ (t - 1)) ∧ ((x14 - x34) ≤ (t - 1))))) : (((x34 - x14) ≤ (t - 1)) ∨ ((x14 - x34) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x34) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause130 (x03 x13 x34 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th7 x03 x13 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 u0)))) h

theorem clause131 (t x12 x13 x23 : ℝ) : (((t + x12 + ((-1) * x13)) ≥ 1) ∨ ((t + ((-1) * x13)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x12 + ((-1) * x13)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th8 t x12 x13 x23
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u2 u3))))) h

theorem clause132 (x23 : ℝ) (h : (x23 ≥ 0)) : ((x23 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause135 (t x12 x13 x23 : ℝ) : (((x12 + ((-1) * x23)) ≥ 1) ∨ ((x12 + ((-1) * x13)) ≤ 0) ∨ (¬ (x12 ≤ x13)) ∨ (¬ (x13 ≤ x23)) ∨ (¬ ((x23 - x12) ≥ 1)) ∨ (¬ ((x13 - x12) ≤ (t - 1))) ∨ (¬ ((x23 - x13) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11 t x12 x13 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause136 (t x12 x13 x23 : ℝ) : (((x12 + ((-1) * x13)) ≤ 0) ∨ ((t + ((-1) * x12) + x13) ≥ 1) ∨ (¬ (x12 ≤ x13)) ∨ (¬ (x13 ≤ x23)) ∨ (¬ ((x23 - x12) ≥ 1)) ∨ (¬ ((x13 - x12) ≤ (t - 1))) ∨ (¬ ((x23 - x13) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x12) + x13) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11 t x12 x13 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause139 (t x12 x13 x23 : ℝ) : (((x13 + ((-1) * x23)) ≤ 0) ∨ ((x12 + ((-1) * x13)) ≥ 0) ∨ (¬ (x12 ≤ x13)) ∨ (¬ (x13 ≤ x23)) ∨ (¬ ((x23 - x12) ≥ 1)) ∨ (¬ ((x13 - x12) ≤ (t - 1))) ∨ (¬ ((x23 - x13) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x13)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11 t x12 x13 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause140 (t x12 x13 x23 : ℝ) : (((x12 + ((-1) * x23)) ≥ 1) ∨ ((x13 + ((-1) * x23)) ≤ 0) ∨ (¬ (x12 ≤ x13)) ∨ (¬ (x13 ≤ x23)) ∨ (¬ ((x23 - x12) ≥ 1)) ∨ (¬ ((x13 - x12) ≤ (t - 1))) ∨ (¬ ((x23 - x13) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11 t x12 x13 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause142 (t x12 x13 x23 : ℝ) : (((x13 + ((-1) * x23)) ≤ 0) ∨ ((t + ((-1) * x13) + x23) ≥ 1) ∨ (¬ (x12 ≤ x13)) ∨ (¬ (x13 ≤ x23)) ∨ (¬ ((x23 - x12) ≥ 1)) ∨ (¬ ((x13 - x12) ≤ (t - 1))) ∨ (¬ ((x23 - x13) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x13) + x23) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11 t x12 x13 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause143 (t x12 x13 x23 : ℝ) : (((x12 + ((-1) * x23)) ≤ (-1)) ∨ ((x13 + ((-1) * x23)) ≥ 0) ∨ (¬ (x12 ≤ x13)) ∨ (¬ (x13 ≤ x23)) ∨ (¬ ((x23 - x12) ≥ 1)) ∨ (¬ ((x13 - x12) ≤ (t - 1))) ∨ (¬ ((x23 - x13) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x23)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x23)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11 t x12 x13 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause144 (t x12 x13 x23 : ℝ) : (((x12 + ((-1) * x23)) ≤ (-1)) ∨ ((x12 + ((-1) * x13)) ≥ 0) ∨ (¬ (x12 ≤ x13)) ∨ (¬ (x13 ≤ x23)) ∨ (¬ ((x23 - x12) ≥ 1)) ∨ (¬ ((x13 - x12) ≤ (t - 1))) ∨ (¬ ((x23 - x13) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x23)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x13)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11 t x12 x13 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause145 (t x12 x13 x23 : ℝ) : (((x12 + ((-1) * x23)) ≥ 1) ∨ ((x12 + ((-1) * x23)) ≤ (-1)) ∨ (¬ (x12 ≤ x13)) ∨ (¬ (x13 ≤ x23)) ∨ (¬ ((x23 - x12) ≥ 1)) ∨ (¬ ((x13 - x12) ≤ (t - 1))) ∨ (¬ ((x23 - x13) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x23)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11 t x12 x13 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause149 (t x12 x13 x23 : ℝ) : (((t + x12 + ((-1) * x13)) ≥ 1) ∨ ((x12 + ((-1) * x13)) ≥ 0) ∨ (¬ (x12 ≤ x13)) ∨ (¬ (x13 ≤ x23)) ∨ (¬ ((x23 - x12) ≥ 1)) ∨ (¬ ((x13 - x12) ≤ (t - 1))) ∨ (¬ ((x23 - x13) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x12 + ((-1) * x13)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x13)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11 t x12 x13 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause150 (t x12 x13 x23 : ℝ) : (((t + x12 + ((-1) * x13)) ≥ 1) ∨ ((x12 + ((-1) * x23)) ≥ 1) ∨ (¬ (x12 ≤ x13)) ∨ (¬ (x13 ≤ x23)) ∨ (¬ ((x23 - x12) ≥ 1)) ∨ (¬ ((x13 - x12) ≤ (t - 1))) ∨ (¬ ((x23 - x13) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x12 + ((-1) * x13)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11 t x12 x13 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause155 (t x12 x13 x23 : ℝ) : (((x12 + ((-1) * x23)) ≥ 1) ∨ ((t + x13 + ((-1) * x23)) ≥ 1) ∨ (¬ (x12 ≤ x13)) ∨ (¬ (x13 ≤ x23)) ∨ (¬ ((x23 - x12) ≥ 1)) ∨ (¬ ((x13 - x12) ≤ (t - 1))) ∨ (¬ ((x23 - x13) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x13 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11 t x12 x13 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause160 (t x12 x13 x23 : ℝ) : (((x12 + ((-1) * x23)) ≥ 1) ∨ ((x12 + ((-1) * x13)) ≤ 0) ∨ (¬ (x23 ≤ x13)) ∨ (¬ (x13 ≤ x12)) ∨ (¬ ((x12 - x23) ≥ 1)) ∨ (¬ ((x12 - x13) ≤ (t - 1))) ∨ (¬ ((x13 - x23) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11 t x12 x13 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause161 (t x12 x13 x23 : ℝ) : (((x12 + ((-1) * x13)) ≤ 0) ∨ ((t + ((-1) * x12) + x13) ≥ 1) ∨ (¬ (x23 ≤ x13)) ∨ (¬ (x13 ≤ x12)) ∨ (¬ ((x12 - x23) ≥ 1)) ∨ (¬ ((x12 - x13) ≤ (t - 1))) ∨ (¬ ((x13 - x23) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x12) + x13) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11 t x12 x13 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause164 (t x12 x13 x23 : ℝ) : (((x13 + ((-1) * x23)) ≤ 0) ∨ ((x12 + ((-1) * x13)) ≥ 0) ∨ (¬ (x23 ≤ x13)) ∨ (¬ (x13 ≤ x12)) ∨ (¬ ((x12 - x23) ≥ 1)) ∨ (¬ ((x12 - x13) ≤ (t - 1))) ∨ (¬ ((x13 - x23) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x13)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11 t x12 x13 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause165 (t x12 x13 x23 : ℝ) : (((x12 + ((-1) * x23)) ≥ 1) ∨ ((x13 + ((-1) * x23)) ≤ 0) ∨ (¬ (x23 ≤ x13)) ∨ (¬ (x13 ≤ x12)) ∨ (¬ ((x12 - x23) ≥ 1)) ∨ (¬ ((x12 - x13) ≤ (t - 1))) ∨ (¬ ((x13 - x23) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11 t x12 x13 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause167 (t x12 x13 x23 : ℝ) : (((x13 + ((-1) * x23)) ≤ 0) ∨ ((t + ((-1) * x13) + x23) ≥ 1) ∨ (¬ (x23 ≤ x13)) ∨ (¬ (x13 ≤ x12)) ∨ (¬ ((x12 - x23) ≥ 1)) ∨ (¬ ((x12 - x13) ≤ (t - 1))) ∨ (¬ ((x13 - x23) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x13) + x23) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11 t x12 x13 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause168 (t x12 x13 x23 : ℝ) : (((x12 + ((-1) * x23)) ≤ (-1)) ∨ ((x13 + ((-1) * x23)) ≥ 0) ∨ (¬ (x23 ≤ x13)) ∨ (¬ (x13 ≤ x12)) ∨ (¬ ((x12 - x23) ≥ 1)) ∨ (¬ ((x12 - x13) ≤ (t - 1))) ∨ (¬ ((x13 - x23) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x23)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x23)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11 t x12 x13 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause169 (t x12 x13 x23 : ℝ) : (((x12 + ((-1) * x23)) ≤ (-1)) ∨ ((x12 + ((-1) * x13)) ≥ 0) ∨ (¬ (x23 ≤ x13)) ∨ (¬ (x13 ≤ x12)) ∨ (¬ ((x12 - x23) ≥ 1)) ∨ (¬ ((x12 - x13) ≤ (t - 1))) ∨ (¬ ((x13 - x23) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x23)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x13)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11 t x12 x13 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause170 (t x12 x13 x23 : ℝ) : (((x12 + ((-1) * x23)) ≥ 1) ∨ ((x12 + ((-1) * x23)) ≤ (-1)) ∨ (¬ (x23 ≤ x13)) ∨ (¬ (x13 ≤ x12)) ∨ (¬ ((x12 - x23) ≥ 1)) ∨ (¬ ((x12 - x13) ≤ (t - 1))) ∨ (¬ ((x13 - x23) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x23)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11 t x12 x13 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause175 (t x12 x13 x23 : ℝ) : (((t + x12 + ((-1) * x13)) ≥ 1) ∨ ((x12 + ((-1) * x23)) ≥ 1) ∨ (¬ (x23 ≤ x13)) ∨ (¬ (x13 ≤ x12)) ∨ (¬ ((x12 - x23) ≥ 1)) ∨ (¬ ((x12 - x13) ≤ (t - 1))) ∨ (¬ ((x13 - x23) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x12 + ((-1) * x13)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11 t x12 x13 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause180 (t x12 x13 x23 : ℝ) : (((x12 + ((-1) * x23)) ≥ 1) ∨ ((t + x13 + ((-1) * x23)) ≥ 1) ∨ (¬ (x23 ≤ x13)) ∨ (¬ (x13 ≤ x12)) ∨ (¬ ((x12 - x23) ≥ 1)) ∨ (¬ ((x12 - x13) ≤ (t - 1))) ∨ (¬ ((x13 - x23) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x13 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11 t x12 x13 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause233 (t x12 x13 x23 : ℝ) (h : (((x12 ≤ x13) ∧ (x13 ≤ x23) ∧ ((x23 - x12) ≥ 1) ∧ ((x13 - x12) ≤ (t - 1)) ∧ ((x23 - x13) ≤ (t - 1))) ∨ ((x23 ≤ x13) ∧ (x13 ≤ x12) ∧ ((x12 - x23) ≥ 1) ∧ ((x12 - x13) ≤ (t - 1)) ∧ ((x13 - x23) ≤ (t - 1))))) : ((x12 ≤ x13) ∨ (x23 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≤ x13) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x23 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause234 (t x12 x13 x23 : ℝ) (h : (((x12 ≤ x13) ∧ (x13 ≤ x23) ∧ ((x23 - x12) ≥ 1) ∧ ((x13 - x12) ≤ (t - 1)) ∧ ((x23 - x13) ≤ (t - 1))) ∨ ((x23 ≤ x13) ∧ (x13 ≤ x12) ∧ ((x12 - x23) ≥ 1) ∧ ((x12 - x13) ≤ (t - 1)) ∧ ((x13 - x23) ≤ (t - 1))))) : ((x12 ≤ x13) ∨ (x13 ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≤ x13) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x13 ≤ x12) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause235 (t x12 x13 x23 : ℝ) (h : (((x12 ≤ x13) ∧ (x13 ≤ x23) ∧ ((x23 - x12) ≥ 1) ∧ ((x13 - x12) ≤ (t - 1)) ∧ ((x23 - x13) ≤ (t - 1))) ∨ ((x23 ≤ x13) ∧ (x13 ≤ x12) ∧ ((x12 - x23) ≥ 1) ∧ ((x12 - x13) ≤ (t - 1)) ∧ ((x13 - x23) ≤ (t - 1))))) : ((x12 ≤ x13) ∨ ((x12 - x23) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≤ x13) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x23) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause236 (t x12 x13 x23 : ℝ) (h : (((x12 ≤ x13) ∧ (x13 ≤ x23) ∧ ((x23 - x12) ≥ 1) ∧ ((x13 - x12) ≤ (t - 1)) ∧ ((x23 - x13) ≤ (t - 1))) ∨ ((x23 ≤ x13) ∧ (x13 ≤ x12) ∧ ((x12 - x23) ≥ 1) ∧ ((x12 - x13) ≤ (t - 1)) ∧ ((x13 - x23) ≤ (t - 1))))) : ((x12 ≤ x13) ∨ ((x12 - x13) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≤ x13) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x13) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause237 (t x12 x13 x23 : ℝ) (h : (((x12 ≤ x13) ∧ (x13 ≤ x23) ∧ ((x23 - x12) ≥ 1) ∧ ((x13 - x12) ≤ (t - 1)) ∧ ((x23 - x13) ≤ (t - 1))) ∨ ((x23 ≤ x13) ∧ (x13 ≤ x12) ∧ ((x12 - x23) ≥ 1) ∧ ((x12 - x13) ≤ (t - 1)) ∧ ((x13 - x23) ≤ (t - 1))))) : ((x12 ≤ x13) ∨ ((x13 - x23) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≤ x13) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x23) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause238 (t x12 x13 x23 : ℝ) (h : (((x12 ≤ x13) ∧ (x13 ≤ x23) ∧ ((x23 - x12) ≥ 1) ∧ ((x13 - x12) ≤ (t - 1)) ∧ ((x23 - x13) ≤ (t - 1))) ∨ ((x23 ≤ x13) ∧ (x13 ≤ x12) ∧ ((x12 - x23) ≥ 1) ∧ ((x12 - x13) ≤ (t - 1)) ∧ ((x13 - x23) ≤ (t - 1))))) : ((x13 ≤ x23) ∨ (x23 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x23) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x23 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause239 (t x12 x13 x23 : ℝ) (h : (((x12 ≤ x13) ∧ (x13 ≤ x23) ∧ ((x23 - x12) ≥ 1) ∧ ((x13 - x12) ≤ (t - 1)) ∧ ((x23 - x13) ≤ (t - 1))) ∨ ((x23 ≤ x13) ∧ (x13 ≤ x12) ∧ ((x12 - x23) ≥ 1) ∧ ((x12 - x13) ≤ (t - 1)) ∧ ((x13 - x23) ≤ (t - 1))))) : ((x13 ≤ x23) ∨ (x13 ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x23) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x13 ≤ x12) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause240 (t x12 x13 x23 : ℝ) (h : (((x12 ≤ x13) ∧ (x13 ≤ x23) ∧ ((x23 - x12) ≥ 1) ∧ ((x13 - x12) ≤ (t - 1)) ∧ ((x23 - x13) ≤ (t - 1))) ∨ ((x23 ≤ x13) ∧ (x13 ≤ x12) ∧ ((x12 - x23) ≥ 1) ∧ ((x12 - x13) ≤ (t - 1)) ∧ ((x13 - x23) ≤ (t - 1))))) : ((x13 ≤ x23) ∨ ((x12 - x23) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x23) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x23) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause241 (t x12 x13 x23 : ℝ) (h : (((x12 ≤ x13) ∧ (x13 ≤ x23) ∧ ((x23 - x12) ≥ 1) ∧ ((x13 - x12) ≤ (t - 1)) ∧ ((x23 - x13) ≤ (t - 1))) ∨ ((x23 ≤ x13) ∧ (x13 ≤ x12) ∧ ((x12 - x23) ≥ 1) ∧ ((x12 - x13) ≤ (t - 1)) ∧ ((x13 - x23) ≤ (t - 1))))) : ((x13 ≤ x23) ∨ ((x12 - x13) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x23) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x13) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause242 (t x12 x13 x23 : ℝ) (h : (((x12 ≤ x13) ∧ (x13 ≤ x23) ∧ ((x23 - x12) ≥ 1) ∧ ((x13 - x12) ≤ (t - 1)) ∧ ((x23 - x13) ≤ (t - 1))) ∨ ((x23 ≤ x13) ∧ (x13 ≤ x12) ∧ ((x12 - x23) ≥ 1) ∧ ((x12 - x13) ≤ (t - 1)) ∧ ((x13 - x23) ≤ (t - 1))))) : ((x13 ≤ x23) ∨ ((x13 - x23) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x23) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x23) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause243 (t x12 x13 x23 : ℝ) (h : (((x12 ≤ x13) ∧ (x13 ≤ x23) ∧ ((x23 - x12) ≥ 1) ∧ ((x13 - x12) ≤ (t - 1)) ∧ ((x23 - x13) ≤ (t - 1))) ∨ ((x23 ≤ x13) ∧ (x13 ≤ x12) ∧ ((x12 - x23) ≥ 1) ∧ ((x12 - x13) ≤ (t - 1)) ∧ ((x13 - x23) ≤ (t - 1))))) : (((x23 - x12) ≥ 1) ∨ (x23 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 - x12) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x23 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause244 (t x12 x13 x23 : ℝ) (h : (((x12 ≤ x13) ∧ (x13 ≤ x23) ∧ ((x23 - x12) ≥ 1) ∧ ((x13 - x12) ≤ (t - 1)) ∧ ((x23 - x13) ≤ (t - 1))) ∨ ((x23 ≤ x13) ∧ (x13 ≤ x12) ∧ ((x12 - x23) ≥ 1) ∧ ((x12 - x13) ≤ (t - 1)) ∧ ((x13 - x23) ≤ (t - 1))))) : (((x23 - x12) ≥ 1) ∨ (x13 ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 - x12) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x13 ≤ x12) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause245 (t x12 x13 x23 : ℝ) (h : (((x12 ≤ x13) ∧ (x13 ≤ x23) ∧ ((x23 - x12) ≥ 1) ∧ ((x13 - x12) ≤ (t - 1)) ∧ ((x23 - x13) ≤ (t - 1))) ∨ ((x23 ≤ x13) ∧ (x13 ≤ x12) ∧ ((x12 - x23) ≥ 1) ∧ ((x12 - x13) ≤ (t - 1)) ∧ ((x13 - x23) ≤ (t - 1))))) : (((x23 - x12) ≥ 1) ∨ ((x12 - x23) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 - x12) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x23) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause246 (t x12 x13 x23 : ℝ) (h : (((x12 ≤ x13) ∧ (x13 ≤ x23) ∧ ((x23 - x12) ≥ 1) ∧ ((x13 - x12) ≤ (t - 1)) ∧ ((x23 - x13) ≤ (t - 1))) ∨ ((x23 ≤ x13) ∧ (x13 ≤ x12) ∧ ((x12 - x23) ≥ 1) ∧ ((x12 - x13) ≤ (t - 1)) ∧ ((x13 - x23) ≤ (t - 1))))) : (((x23 - x12) ≥ 1) ∨ ((x12 - x13) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 - x12) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x13) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause247 (t x12 x13 x23 : ℝ) (h : (((x12 ≤ x13) ∧ (x13 ≤ x23) ∧ ((x23 - x12) ≥ 1) ∧ ((x13 - x12) ≤ (t - 1)) ∧ ((x23 - x13) ≤ (t - 1))) ∨ ((x23 ≤ x13) ∧ (x13 ≤ x12) ∧ ((x12 - x23) ≥ 1) ∧ ((x12 - x13) ≤ (t - 1)) ∧ ((x13 - x23) ≤ (t - 1))))) : (((x23 - x12) ≥ 1) ∨ ((x13 - x23) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 - x12) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x23) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause248 (t x12 x13 x23 : ℝ) (h : (((x12 ≤ x13) ∧ (x13 ≤ x23) ∧ ((x23 - x12) ≥ 1) ∧ ((x13 - x12) ≤ (t - 1)) ∧ ((x23 - x13) ≤ (t - 1))) ∨ ((x23 ≤ x13) ∧ (x13 ≤ x12) ∧ ((x12 - x23) ≥ 1) ∧ ((x12 - x13) ≤ (t - 1)) ∧ ((x13 - x23) ≤ (t - 1))))) : (((x13 - x12) ≤ (t - 1)) ∨ (x23 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 - x12) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x23 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause249 (t x12 x13 x23 : ℝ) (h : (((x12 ≤ x13) ∧ (x13 ≤ x23) ∧ ((x23 - x12) ≥ 1) ∧ ((x13 - x12) ≤ (t - 1)) ∧ ((x23 - x13) ≤ (t - 1))) ∨ ((x23 ≤ x13) ∧ (x13 ≤ x12) ∧ ((x12 - x23) ≥ 1) ∧ ((x12 - x13) ≤ (t - 1)) ∧ ((x13 - x23) ≤ (t - 1))))) : (((x13 - x12) ≤ (t - 1)) ∨ (x13 ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 - x12) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x13 ≤ x12) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause250 (t x12 x13 x23 : ℝ) (h : (((x12 ≤ x13) ∧ (x13 ≤ x23) ∧ ((x23 - x12) ≥ 1) ∧ ((x13 - x12) ≤ (t - 1)) ∧ ((x23 - x13) ≤ (t - 1))) ∨ ((x23 ≤ x13) ∧ (x13 ≤ x12) ∧ ((x12 - x23) ≥ 1) ∧ ((x12 - x13) ≤ (t - 1)) ∧ ((x13 - x23) ≤ (t - 1))))) : (((x13 - x12) ≤ (t - 1)) ∨ ((x12 - x23) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 - x12) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x23) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause251 (t x12 x13 x23 : ℝ) (h : (((x12 ≤ x13) ∧ (x13 ≤ x23) ∧ ((x23 - x12) ≥ 1) ∧ ((x13 - x12) ≤ (t - 1)) ∧ ((x23 - x13) ≤ (t - 1))) ∨ ((x23 ≤ x13) ∧ (x13 ≤ x12) ∧ ((x12 - x23) ≥ 1) ∧ ((x12 - x13) ≤ (t - 1)) ∧ ((x13 - x23) ≤ (t - 1))))) : (((x13 - x12) ≤ (t - 1)) ∨ ((x12 - x13) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 - x12) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x13) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause252 (t x12 x13 x23 : ℝ) (h : (((x12 ≤ x13) ∧ (x13 ≤ x23) ∧ ((x23 - x12) ≥ 1) ∧ ((x13 - x12) ≤ (t - 1)) ∧ ((x23 - x13) ≤ (t - 1))) ∨ ((x23 ≤ x13) ∧ (x13 ≤ x12) ∧ ((x12 - x23) ≥ 1) ∧ ((x12 - x13) ≤ (t - 1)) ∧ ((x13 - x23) ≤ (t - 1))))) : (((x13 - x12) ≤ (t - 1)) ∨ ((x13 - x23) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 - x12) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x23) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause253 (t x12 x13 x23 : ℝ) (h : (((x12 ≤ x13) ∧ (x13 ≤ x23) ∧ ((x23 - x12) ≥ 1) ∧ ((x13 - x12) ≤ (t - 1)) ∧ ((x23 - x13) ≤ (t - 1))) ∨ ((x23 ≤ x13) ∧ (x13 ≤ x12) ∧ ((x12 - x23) ≥ 1) ∧ ((x12 - x13) ≤ (t - 1)) ∧ ((x13 - x23) ≤ (t - 1))))) : (((x23 - x13) ≤ (t - 1)) ∨ (x23 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x23 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause254 (t x12 x13 x23 : ℝ) (h : (((x12 ≤ x13) ∧ (x13 ≤ x23) ∧ ((x23 - x12) ≥ 1) ∧ ((x13 - x12) ≤ (t - 1)) ∧ ((x23 - x13) ≤ (t - 1))) ∨ ((x23 ≤ x13) ∧ (x13 ≤ x12) ∧ ((x12 - x23) ≥ 1) ∧ ((x12 - x13) ≤ (t - 1)) ∧ ((x13 - x23) ≤ (t - 1))))) : (((x23 - x13) ≤ (t - 1)) ∨ (x13 ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x13 ≤ x12) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause255 (t x12 x13 x23 : ℝ) (h : (((x12 ≤ x13) ∧ (x13 ≤ x23) ∧ ((x23 - x12) ≥ 1) ∧ ((x13 - x12) ≤ (t - 1)) ∧ ((x23 - x13) ≤ (t - 1))) ∨ ((x23 ≤ x13) ∧ (x13 ≤ x12) ∧ ((x12 - x23) ≥ 1) ∧ ((x12 - x13) ≤ (t - 1)) ∧ ((x13 - x23) ≤ (t - 1))))) : (((x23 - x13) ≤ (t - 1)) ∨ ((x12 - x23) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x23) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause256 (t x12 x13 x23 : ℝ) (h : (((x12 ≤ x13) ∧ (x13 ≤ x23) ∧ ((x23 - x12) ≥ 1) ∧ ((x13 - x12) ≤ (t - 1)) ∧ ((x23 - x13) ≤ (t - 1))) ∨ ((x23 ≤ x13) ∧ (x13 ≤ x12) ∧ ((x12 - x23) ≥ 1) ∧ ((x12 - x13) ≤ (t - 1)) ∧ ((x13 - x23) ≤ (t - 1))))) : (((x23 - x13) ≤ (t - 1)) ∨ ((x12 - x13) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x13) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause257 (t x12 x13 x23 : ℝ) (h : (((x12 ≤ x13) ∧ (x13 ≤ x23) ∧ ((x23 - x12) ≥ 1) ∧ ((x13 - x12) ≤ (t - 1)) ∧ ((x23 - x13) ≤ (t - 1))) ∨ ((x23 ≤ x13) ∧ (x13 ≤ x12) ∧ ((x12 - x23) ≥ 1) ∧ ((x12 - x13) ≤ (t - 1)) ∧ ((x13 - x23) ≤ (t - 1))))) : (((x23 - x13) ≤ (t - 1)) ∨ ((x13 - x23) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x23) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause258 (t x13 : ℝ) : ((¬ ((t + ((-1) * x13)) ≤ 0)) ∨ (t ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x13) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th13 t x13
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause260 (t x13 : ℝ) : ((¬ (t ≤ x13)) ∨ (¬ (x13 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x13 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th14 t x13
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause262 (t x13 : ℝ) (h : (x13 < t)) : ((x13 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 < t) := fun hh => hn hh
  exact u0 h

theorem clause263 (t x01 x03 x12 x13 x34 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x03)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x12 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th16 t x01 x03 x12 x13 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u0 u5))))))) h

theorem clause264 (t : ℝ) : ((¬ (t ≥ (7 / 2))) ∨ ((7 / 2) ≤ t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≥ (7 / 2)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((7 / 2) ≤ t) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th17 t
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause266 (t : ℝ) : ((¬ ((7 / 2) ≤ t)) ∨ (¬ ((7 / 2) > t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((7 / 2) ≤ t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((7 / 2) > t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th18 t
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause268 (t : ℝ) (h : ((7 / 2) > t)) : (((7 / 2) > t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((7 / 2) > t) := fun hh => hn hh
  exact u0 h

theorem clause269 (t x01 x03 x13 : ℝ) : (((x03 + ((-1) * x13)) ≥ 0) ∨ ((x01 + ((-1) * x03)) ≤ 0) ∨ (¬ (x01 ≤ x03)) ∨ (¬ (x03 ≤ x13)) ∨ (¬ ((x13 - x01) ≥ 1)) ∨ (¬ ((x03 - x01) ≤ (t - 1))) ∨ (¬ ((x13 - x03) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x13)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x03)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th23 t x01 x03 x13
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause271 (t x01 x03 x13 : ℝ) : (((x01 + ((-1) * x13)) ≥ 1) ∨ ((x01 + ((-1) * x03)) ≤ 0) ∨ (¬ (x01 ≤ x03)) ∨ (¬ (x03 ≤ x13)) ∨ (¬ ((x13 - x01) ≥ 1)) ∨ (¬ ((x03 - x01) ≤ (t - 1))) ∨ (¬ ((x13 - x03) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x13)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x03)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th23 t x01 x03 x13
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause272 (t x01 x03 x13 : ℝ) : (((t + ((-1) * x01) + x03) ≥ 1) ∨ ((x01 + ((-1) * x03)) ≤ 0) ∨ (¬ (x01 ≤ x03)) ∨ (¬ (x03 ≤ x13)) ∨ (¬ ((x13 - x01) ≥ 1)) ∨ (¬ ((x03 - x01) ≤ (t - 1))) ∨ (¬ ((x13 - x03) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x01) + x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x03)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th23 t x01 x03 x13
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause275 (t x01 x03 x13 : ℝ) : (((x03 + ((-1) * x13)) ≤ 0) ∨ ((x01 + ((-1) * x03)) ≥ 0) ∨ (¬ (x01 ≤ x03)) ∨ (¬ (x03 ≤ x13)) ∨ (¬ ((x13 - x01) ≥ 1)) ∨ (¬ ((x03 - x01) ≤ (t - 1))) ∨ (¬ ((x13 - x03) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x03)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th23 t x01 x03 x13
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause276 (t x01 x03 x13 : ℝ) : (((x01 + ((-1) * x13)) ≥ 1) ∨ ((x03 + ((-1) * x13)) ≤ 0) ∨ (¬ (x01 ≤ x03)) ∨ (¬ (x03 ≤ x13)) ∨ (¬ ((x13 - x01) ≥ 1)) ∨ (¬ ((x03 - x01) ≤ (t - 1))) ∨ (¬ ((x13 - x03) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x13)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th23 t x01 x03 x13
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause277 (t x01 x03 x13 : ℝ) : (((t + ((-1) * x01) + x03) ≥ 1) ∨ ((x03 + ((-1) * x13)) ≤ 0) ∨ (¬ (x01 ≤ x03)) ∨ (¬ (x03 ≤ x13)) ∨ (¬ ((x13 - x01) ≥ 1)) ∨ (¬ ((x03 - x01) ≤ (t - 1))) ∨ (¬ ((x13 - x03) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x01) + x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th23 t x01 x03 x13
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause279 (t x01 x03 x13 : ℝ) : (((x03 + ((-1) * x13)) ≥ 0) ∨ ((x01 + ((-1) * x13)) ≤ (-1)) ∨ (¬ (x01 ≤ x03)) ∨ (¬ (x03 ≤ x13)) ∨ (¬ ((x13 - x01) ≥ 1)) ∨ (¬ ((x03 - x01) ≤ (t - 1))) ∨ (¬ ((x13 - x03) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x13)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x13)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th23 t x01 x03 x13
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause280 (t x01 x03 x13 : ℝ) : (((x01 + ((-1) * x13)) ≤ (-1)) ∨ ((x01 + ((-1) * x03)) ≥ 0) ∨ (¬ (x01 ≤ x03)) ∨ (¬ (x03 ≤ x13)) ∨ (¬ ((x13 - x01) ≥ 1)) ∨ (¬ ((x03 - x01) ≤ (t - 1))) ∨ (¬ ((x13 - x03) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x13)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x03)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th23 t x01 x03 x13
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause281 (t x01 x03 x13 : ℝ) : (((x01 + ((-1) * x13)) ≥ 1) ∨ ((x01 + ((-1) * x13)) ≤ (-1)) ∨ (¬ (x01 ≤ x03)) ∨ (¬ (x03 ≤ x13)) ∨ (¬ ((x13 - x01) ≥ 1)) ∨ (¬ ((x03 - x01) ≤ (t - 1))) ∨ (¬ ((x13 - x03) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x13)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x13)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th23 t x01 x03 x13
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause283 (t x01 x03 x13 : ℝ) : (((x01 + ((-1) * x13)) ≤ (-1)) ∨ ((t + ((-1) * x03) + x13) ≥ 1) ∨ (¬ (x01 ≤ x03)) ∨ (¬ (x03 ≤ x13)) ∨ (¬ ((x13 - x01) ≥ 1)) ∨ (¬ ((x03 - x01) ≤ (t - 1))) ∨ (¬ ((x13 - x03) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x13)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x03) + x13) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th23 t x01 x03 x13
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause286 (t x01 x03 x13 : ℝ) : (((x01 + ((-1) * x13)) ≥ 1) ∨ ((t + x01 + ((-1) * x03)) ≥ 1) ∨ (¬ (x01 ≤ x03)) ∨ (¬ (x03 ≤ x13)) ∨ (¬ ((x13 - x01) ≥ 1)) ∨ (¬ ((x03 - x01) ≤ (t - 1))) ∨ (¬ ((x13 - x03) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x13)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x01 + ((-1) * x03)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th23 t x01 x03 x13
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause289 (t x01 x03 x13 : ℝ) : (((x03 + ((-1) * x13)) ≥ 0) ∨ ((t + x03 + ((-1) * x13)) ≥ 1) ∨ (¬ (x01 ≤ x03)) ∨ (¬ (x03 ≤ x13)) ∨ (¬ ((x13 - x01) ≥ 1)) ∨ (¬ ((x03 - x01) ≤ (t - 1))) ∨ (¬ ((x13 - x03) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x13)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x03 + ((-1) * x13)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th23 t x01 x03 x13
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause296 (t x01 x03 x13 : ℝ) : (((x01 + ((-1) * x13)) ≥ 1) ∨ ((x01 + ((-1) * x03)) ≤ 0) ∨ (¬ (x13 ≤ x03)) ∨ (¬ (x03 ≤ x01)) ∨ (¬ ((x01 - x13) ≥ 1)) ∨ (¬ ((x01 - x03) ≤ (t - 1))) ∨ (¬ ((x03 - x13) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x13)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x03)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th23 t x01 x03 x13
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause297 (t x01 x03 x13 : ℝ) : (((t + ((-1) * x01) + x03) ≥ 1) ∨ ((x01 + ((-1) * x03)) ≤ 0) ∨ (¬ (x13 ≤ x03)) ∨ (¬ (x03 ≤ x01)) ∨ (¬ ((x01 - x13) ≥ 1)) ∨ (¬ ((x01 - x03) ≤ (t - 1))) ∨ (¬ ((x03 - x13) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x01) + x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x03)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th23 t x01 x03 x13
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause300 (t x01 x03 x13 : ℝ) : (((x03 + ((-1) * x13)) ≤ 0) ∨ ((x01 + ((-1) * x03)) ≥ 0) ∨ (¬ (x13 ≤ x03)) ∨ (¬ (x03 ≤ x01)) ∨ (¬ ((x01 - x13) ≥ 1)) ∨ (¬ ((x01 - x03) ≤ (t - 1))) ∨ (¬ ((x03 - x13) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x03)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th23 t x01 x03 x13
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause301 (t x01 x03 x13 : ℝ) : (((x01 + ((-1) * x13)) ≥ 1) ∨ ((x03 + ((-1) * x13)) ≤ 0) ∨ (¬ (x13 ≤ x03)) ∨ (¬ (x03 ≤ x01)) ∨ (¬ ((x01 - x13) ≥ 1)) ∨ (¬ ((x01 - x03) ≤ (t - 1))) ∨ (¬ ((x03 - x13) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x13)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th23 t x01 x03 x13
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause302 (t x01 x03 x13 : ℝ) : (((t + ((-1) * x01) + x03) ≥ 1) ∨ ((x03 + ((-1) * x13)) ≤ 0) ∨ (¬ (x13 ≤ x03)) ∨ (¬ (x03 ≤ x01)) ∨ (¬ ((x01 - x13) ≥ 1)) ∨ (¬ ((x01 - x03) ≤ (t - 1))) ∨ (¬ ((x03 - x13) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x01) + x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th23 t x01 x03 x13
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause303 (t x01 x03 x13 : ℝ) : (((x03 + ((-1) * x13)) ≤ 0) ∨ ((t + ((-1) * x03) + x13) ≥ 1) ∨ (¬ (x13 ≤ x03)) ∨ (¬ (x03 ≤ x01)) ∨ (¬ ((x01 - x13) ≥ 1)) ∨ (¬ ((x01 - x03) ≤ (t - 1))) ∨ (¬ ((x03 - x13) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x03) + x13) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th23 t x01 x03 x13
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause304 (t x01 x03 x13 : ℝ) : (((x03 + ((-1) * x13)) ≥ 0) ∨ ((x01 + ((-1) * x13)) ≤ (-1)) ∨ (¬ (x13 ≤ x03)) ∨ (¬ (x03 ≤ x01)) ∨ (¬ ((x01 - x13) ≥ 1)) ∨ (¬ ((x01 - x03) ≤ (t - 1))) ∨ (¬ ((x03 - x13) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x13)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x13)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th23 t x01 x03 x13
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause305 (t x01 x03 x13 : ℝ) : (((x01 + ((-1) * x13)) ≤ (-1)) ∨ ((x01 + ((-1) * x03)) ≥ 0) ∨ (¬ (x13 ≤ x03)) ∨ (¬ (x03 ≤ x01)) ∨ (¬ ((x01 - x13) ≥ 1)) ∨ (¬ ((x01 - x03) ≤ (t - 1))) ∨ (¬ ((x03 - x13) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x13)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x03)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th23 t x01 x03 x13
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause306 (t x01 x03 x13 : ℝ) : (((x01 + ((-1) * x13)) ≥ 1) ∨ ((x01 + ((-1) * x13)) ≤ (-1)) ∨ (¬ (x13 ≤ x03)) ∨ (¬ (x03 ≤ x01)) ∨ (¬ ((x01 - x13) ≥ 1)) ∨ (¬ ((x01 - x03) ≤ (t - 1))) ∨ (¬ ((x03 - x13) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x13)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x13)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th23 t x01 x03 x13
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause307 (t x01 x03 x13 : ℝ) : (((t + ((-1) * x01) + x03) ≥ 1) ∨ ((x01 + ((-1) * x13)) ≤ (-1)) ∨ (¬ (x13 ≤ x03)) ∨ (¬ (x03 ≤ x01)) ∨ (¬ ((x01 - x13) ≥ 1)) ∨ (¬ ((x01 - x03) ≤ (t - 1))) ∨ (¬ ((x03 - x13) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x01) + x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x13)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th23 t x01 x03 x13
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause311 (t x01 x03 x13 : ℝ) : (((x01 + ((-1) * x13)) ≥ 1) ∨ ((t + x01 + ((-1) * x03)) ≥ 1) ∨ (¬ (x13 ≤ x03)) ∨ (¬ (x03 ≤ x01)) ∨ (¬ ((x01 - x13) ≥ 1)) ∨ (¬ ((x01 - x03) ≤ (t - 1))) ∨ (¬ ((x03 - x13) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x13)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x01 + ((-1) * x03)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th23 t x01 x03 x13
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause314 (t x01 x03 x13 : ℝ) : (((x03 + ((-1) * x13)) ≥ 0) ∨ ((t + x03 + ((-1) * x13)) ≥ 1) ∨ (¬ (x13 ≤ x03)) ∨ (¬ (x03 ≤ x01)) ∨ (¬ ((x01 - x13) ≥ 1)) ∨ (¬ ((x01 - x03) ≤ (t - 1))) ∨ (¬ ((x03 - x13) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x13)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x03 + ((-1) * x13)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th23 t x01 x03 x13
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause369 (t x01 x03 x13 : ℝ) (h : (((x01 ≤ x03) ∧ (x03 ≤ x13) ∧ ((x13 - x01) ≥ 1) ∧ ((x03 - x01) ≤ (t - 1)) ∧ ((x13 - x03) ≤ (t - 1))) ∨ ((x13 ≤ x03) ∧ (x03 ≤ x01) ∧ ((x01 - x13) ≥ 1) ∧ ((x01 - x03) ≤ (t - 1)) ∧ ((x03 - x13) ≤ (t - 1))))) : ((x01 ≤ x03) ∨ (x13 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x03) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x13 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause370 (t x01 x03 x13 : ℝ) (h : (((x01 ≤ x03) ∧ (x03 ≤ x13) ∧ ((x13 - x01) ≥ 1) ∧ ((x03 - x01) ≤ (t - 1)) ∧ ((x13 - x03) ≤ (t - 1))) ∨ ((x13 ≤ x03) ∧ (x03 ≤ x01) ∧ ((x01 - x13) ≥ 1) ∧ ((x01 - x03) ≤ (t - 1)) ∧ ((x03 - x13) ≤ (t - 1))))) : ((x01 ≤ x03) ∨ (x03 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x03) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x03 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause371 (t x01 x03 x13 : ℝ) (h : (((x01 ≤ x03) ∧ (x03 ≤ x13) ∧ ((x13 - x01) ≥ 1) ∧ ((x03 - x01) ≤ (t - 1)) ∧ ((x13 - x03) ≤ (t - 1))) ∨ ((x13 ≤ x03) ∧ (x03 ≤ x01) ∧ ((x01 - x13) ≥ 1) ∧ ((x01 - x03) ≤ (t - 1)) ∧ ((x03 - x13) ≤ (t - 1))))) : ((x01 ≤ x03) ∨ ((x01 - x13) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x03) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x13) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause372 (t x01 x03 x13 : ℝ) (h : (((x01 ≤ x03) ∧ (x03 ≤ x13) ∧ ((x13 - x01) ≥ 1) ∧ ((x03 - x01) ≤ (t - 1)) ∧ ((x13 - x03) ≤ (t - 1))) ∨ ((x13 ≤ x03) ∧ (x03 ≤ x01) ∧ ((x01 - x13) ≥ 1) ∧ ((x01 - x03) ≤ (t - 1)) ∧ ((x03 - x13) ≤ (t - 1))))) : ((x01 ≤ x03) ∨ ((x01 - x03) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x03) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x03) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause373 (t x01 x03 x13 : ℝ) (h : (((x01 ≤ x03) ∧ (x03 ≤ x13) ∧ ((x13 - x01) ≥ 1) ∧ ((x03 - x01) ≤ (t - 1)) ∧ ((x13 - x03) ≤ (t - 1))) ∨ ((x13 ≤ x03) ∧ (x03 ≤ x01) ∧ ((x01 - x13) ≥ 1) ∧ ((x01 - x03) ≤ (t - 1)) ∧ ((x03 - x13) ≤ (t - 1))))) : ((x01 ≤ x03) ∨ ((x03 - x13) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x03) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x13) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause374 (t x01 x03 x13 : ℝ) (h : (((x01 ≤ x03) ∧ (x03 ≤ x13) ∧ ((x13 - x01) ≥ 1) ∧ ((x03 - x01) ≤ (t - 1)) ∧ ((x13 - x03) ≤ (t - 1))) ∨ ((x13 ≤ x03) ∧ (x03 ≤ x01) ∧ ((x01 - x13) ≥ 1) ∧ ((x01 - x03) ≤ (t - 1)) ∧ ((x03 - x13) ≤ (t - 1))))) : ((x03 ≤ x13) ∨ (x13 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x13) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x13 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause375 (t x01 x03 x13 : ℝ) (h : (((x01 ≤ x03) ∧ (x03 ≤ x13) ∧ ((x13 - x01) ≥ 1) ∧ ((x03 - x01) ≤ (t - 1)) ∧ ((x13 - x03) ≤ (t - 1))) ∨ ((x13 ≤ x03) ∧ (x03 ≤ x01) ∧ ((x01 - x13) ≥ 1) ∧ ((x01 - x03) ≤ (t - 1)) ∧ ((x03 - x13) ≤ (t - 1))))) : ((x03 ≤ x13) ∨ (x03 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x13) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x03 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause376 (t x01 x03 x13 : ℝ) (h : (((x01 ≤ x03) ∧ (x03 ≤ x13) ∧ ((x13 - x01) ≥ 1) ∧ ((x03 - x01) ≤ (t - 1)) ∧ ((x13 - x03) ≤ (t - 1))) ∨ ((x13 ≤ x03) ∧ (x03 ≤ x01) ∧ ((x01 - x13) ≥ 1) ∧ ((x01 - x03) ≤ (t - 1)) ∧ ((x03 - x13) ≤ (t - 1))))) : ((x03 ≤ x13) ∨ ((x01 - x13) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x13) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x13) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause377 (t x01 x03 x13 : ℝ) (h : (((x01 ≤ x03) ∧ (x03 ≤ x13) ∧ ((x13 - x01) ≥ 1) ∧ ((x03 - x01) ≤ (t - 1)) ∧ ((x13 - x03) ≤ (t - 1))) ∨ ((x13 ≤ x03) ∧ (x03 ≤ x01) ∧ ((x01 - x13) ≥ 1) ∧ ((x01 - x03) ≤ (t - 1)) ∧ ((x03 - x13) ≤ (t - 1))))) : ((x03 ≤ x13) ∨ ((x01 - x03) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x13) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x03) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause378 (t x01 x03 x13 : ℝ) (h : (((x01 ≤ x03) ∧ (x03 ≤ x13) ∧ ((x13 - x01) ≥ 1) ∧ ((x03 - x01) ≤ (t - 1)) ∧ ((x13 - x03) ≤ (t - 1))) ∨ ((x13 ≤ x03) ∧ (x03 ≤ x01) ∧ ((x01 - x13) ≥ 1) ∧ ((x01 - x03) ≤ (t - 1)) ∧ ((x03 - x13) ≤ (t - 1))))) : ((x03 ≤ x13) ∨ ((x03 - x13) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x13) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x13) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause379 (t x01 x03 x13 : ℝ) (h : (((x01 ≤ x03) ∧ (x03 ≤ x13) ∧ ((x13 - x01) ≥ 1) ∧ ((x03 - x01) ≤ (t - 1)) ∧ ((x13 - x03) ≤ (t - 1))) ∨ ((x13 ≤ x03) ∧ (x03 ≤ x01) ∧ ((x01 - x13) ≥ 1) ∧ ((x01 - x03) ≤ (t - 1)) ∧ ((x03 - x13) ≤ (t - 1))))) : (((x13 - x01) ≥ 1) ∨ (x13 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x13 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause380 (t x01 x03 x13 : ℝ) (h : (((x01 ≤ x03) ∧ (x03 ≤ x13) ∧ ((x13 - x01) ≥ 1) ∧ ((x03 - x01) ≤ (t - 1)) ∧ ((x13 - x03) ≤ (t - 1))) ∨ ((x13 ≤ x03) ∧ (x03 ≤ x01) ∧ ((x01 - x13) ≥ 1) ∧ ((x01 - x03) ≤ (t - 1)) ∧ ((x03 - x13) ≤ (t - 1))))) : (((x13 - x01) ≥ 1) ∨ (x03 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x03 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause381 (t x01 x03 x13 : ℝ) (h : (((x01 ≤ x03) ∧ (x03 ≤ x13) ∧ ((x13 - x01) ≥ 1) ∧ ((x03 - x01) ≤ (t - 1)) ∧ ((x13 - x03) ≤ (t - 1))) ∨ ((x13 ≤ x03) ∧ (x03 ≤ x01) ∧ ((x01 - x13) ≥ 1) ∧ ((x01 - x03) ≤ (t - 1)) ∧ ((x03 - x13) ≤ (t - 1))))) : (((x13 - x01) ≥ 1) ∨ ((x01 - x13) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x13) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause382 (t x01 x03 x13 : ℝ) (h : (((x01 ≤ x03) ∧ (x03 ≤ x13) ∧ ((x13 - x01) ≥ 1) ∧ ((x03 - x01) ≤ (t - 1)) ∧ ((x13 - x03) ≤ (t - 1))) ∨ ((x13 ≤ x03) ∧ (x03 ≤ x01) ∧ ((x01 - x13) ≥ 1) ∧ ((x01 - x03) ≤ (t - 1)) ∧ ((x03 - x13) ≤ (t - 1))))) : (((x13 - x01) ≥ 1) ∨ ((x01 - x03) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x03) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause383 (t x01 x03 x13 : ℝ) (h : (((x01 ≤ x03) ∧ (x03 ≤ x13) ∧ ((x13 - x01) ≥ 1) ∧ ((x03 - x01) ≤ (t - 1)) ∧ ((x13 - x03) ≤ (t - 1))) ∨ ((x13 ≤ x03) ∧ (x03 ≤ x01) ∧ ((x01 - x13) ≥ 1) ∧ ((x01 - x03) ≤ (t - 1)) ∧ ((x03 - x13) ≤ (t - 1))))) : (((x13 - x01) ≥ 1) ∨ ((x03 - x13) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x13) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause384 (t x01 x03 x13 : ℝ) (h : (((x01 ≤ x03) ∧ (x03 ≤ x13) ∧ ((x13 - x01) ≥ 1) ∧ ((x03 - x01) ≤ (t - 1)) ∧ ((x13 - x03) ≤ (t - 1))) ∨ ((x13 ≤ x03) ∧ (x03 ≤ x01) ∧ ((x01 - x13) ≥ 1) ∧ ((x01 - x03) ≤ (t - 1)) ∧ ((x03 - x13) ≤ (t - 1))))) : (((x03 - x01) ≤ (t - 1)) ∨ (x13 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x13 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause385 (t x01 x03 x13 : ℝ) (h : (((x01 ≤ x03) ∧ (x03 ≤ x13) ∧ ((x13 - x01) ≥ 1) ∧ ((x03 - x01) ≤ (t - 1)) ∧ ((x13 - x03) ≤ (t - 1))) ∨ ((x13 ≤ x03) ∧ (x03 ≤ x01) ∧ ((x01 - x13) ≥ 1) ∧ ((x01 - x03) ≤ (t - 1)) ∧ ((x03 - x13) ≤ (t - 1))))) : (((x03 - x01) ≤ (t - 1)) ∨ (x03 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x03 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause386 (t x01 x03 x13 : ℝ) (h : (((x01 ≤ x03) ∧ (x03 ≤ x13) ∧ ((x13 - x01) ≥ 1) ∧ ((x03 - x01) ≤ (t - 1)) ∧ ((x13 - x03) ≤ (t - 1))) ∨ ((x13 ≤ x03) ∧ (x03 ≤ x01) ∧ ((x01 - x13) ≥ 1) ∧ ((x01 - x03) ≤ (t - 1)) ∧ ((x03 - x13) ≤ (t - 1))))) : (((x03 - x01) ≤ (t - 1)) ∨ ((x01 - x13) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x13) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause387 (t x01 x03 x13 : ℝ) (h : (((x01 ≤ x03) ∧ (x03 ≤ x13) ∧ ((x13 - x01) ≥ 1) ∧ ((x03 - x01) ≤ (t - 1)) ∧ ((x13 - x03) ≤ (t - 1))) ∨ ((x13 ≤ x03) ∧ (x03 ≤ x01) ∧ ((x01 - x13) ≥ 1) ∧ ((x01 - x03) ≤ (t - 1)) ∧ ((x03 - x13) ≤ (t - 1))))) : (((x03 - x01) ≤ (t - 1)) ∨ ((x01 - x03) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x03) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause388 (t x01 x03 x13 : ℝ) (h : (((x01 ≤ x03) ∧ (x03 ≤ x13) ∧ ((x13 - x01) ≥ 1) ∧ ((x03 - x01) ≤ (t - 1)) ∧ ((x13 - x03) ≤ (t - 1))) ∨ ((x13 ≤ x03) ∧ (x03 ≤ x01) ∧ ((x01 - x13) ≥ 1) ∧ ((x01 - x03) ≤ (t - 1)) ∧ ((x03 - x13) ≤ (t - 1))))) : (((x03 - x01) ≤ (t - 1)) ∨ ((x03 - x13) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x13) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause389 (t x01 x03 x13 : ℝ) (h : (((x01 ≤ x03) ∧ (x03 ≤ x13) ∧ ((x13 - x01) ≥ 1) ∧ ((x03 - x01) ≤ (t - 1)) ∧ ((x13 - x03) ≤ (t - 1))) ∨ ((x13 ≤ x03) ∧ (x03 ≤ x01) ∧ ((x01 - x13) ≥ 1) ∧ ((x01 - x03) ≤ (t - 1)) ∧ ((x03 - x13) ≤ (t - 1))))) : (((x13 - x03) ≤ (t - 1)) ∨ (x13 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x13 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause390 (t x01 x03 x13 : ℝ) (h : (((x01 ≤ x03) ∧ (x03 ≤ x13) ∧ ((x13 - x01) ≥ 1) ∧ ((x03 - x01) ≤ (t - 1)) ∧ ((x13 - x03) ≤ (t - 1))) ∨ ((x13 ≤ x03) ∧ (x03 ≤ x01) ∧ ((x01 - x13) ≥ 1) ∧ ((x01 - x03) ≤ (t - 1)) ∧ ((x03 - x13) ≤ (t - 1))))) : (((x13 - x03) ≤ (t - 1)) ∨ (x03 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x03 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause391 (t x01 x03 x13 : ℝ) (h : (((x01 ≤ x03) ∧ (x03 ≤ x13) ∧ ((x13 - x01) ≥ 1) ∧ ((x03 - x01) ≤ (t - 1)) ∧ ((x13 - x03) ≤ (t - 1))) ∨ ((x13 ≤ x03) ∧ (x03 ≤ x01) ∧ ((x01 - x13) ≥ 1) ∧ ((x01 - x03) ≤ (t - 1)) ∧ ((x03 - x13) ≤ (t - 1))))) : (((x13 - x03) ≤ (t - 1)) ∨ ((x01 - x13) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x13) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause392 (t x01 x03 x13 : ℝ) (h : (((x01 ≤ x03) ∧ (x03 ≤ x13) ∧ ((x13 - x01) ≥ 1) ∧ ((x03 - x01) ≤ (t - 1)) ∧ ((x13 - x03) ≤ (t - 1))) ∨ ((x13 ≤ x03) ∧ (x03 ≤ x01) ∧ ((x01 - x13) ≥ 1) ∧ ((x01 - x03) ≤ (t - 1)) ∧ ((x03 - x13) ≤ (t - 1))))) : (((x13 - x03) ≤ (t - 1)) ∨ ((x01 - x03) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x03) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause393 (t x01 x03 x13 : ℝ) (h : (((x01 ≤ x03) ∧ (x03 ≤ x13) ∧ ((x13 - x01) ≥ 1) ∧ ((x03 - x01) ≤ (t - 1)) ∧ ((x13 - x03) ≤ (t - 1))) ∨ ((x13 ≤ x03) ∧ (x03 ≤ x01) ∧ ((x01 - x13) ≥ 1) ∧ ((x01 - x03) ≤ (t - 1)) ∧ ((x03 - x13) ≤ (t - 1))))) : (((x13 - x03) ≤ (t - 1)) ∨ ((x03 - x13) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x13) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause394 (t x01 x02 x12 : ℝ) : (((x01 + ((-1) * x02)) ≤ 0) ∨ ((x02 + ((-1) * x12)) ≥ 0) ∨ (¬ (x01 ≤ x02)) ∨ (¬ (x02 ≤ x12)) ∨ (¬ ((x12 - x01) ≥ 1)) ∨ (¬ ((x02 - x01) ≤ (t - 1))) ∨ (¬ ((x12 - x02) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x12)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th26 t x01 x02 x12
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause400 (t x01 x02 x12 : ℝ) : (((x02 + ((-1) * x12)) ≤ 0) ∨ ((x01 + ((-1) * x02)) ≥ 0) ∨ (¬ (x01 ≤ x02)) ∨ (¬ (x02 ≤ x12)) ∨ (¬ ((x12 - x01) ≥ 1)) ∨ (¬ ((x02 - x01) ≤ (t - 1))) ∨ (¬ ((x12 - x02) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x02)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th26 t x01 x02 x12
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause403 (t x01 x02 x12 : ℝ) : (((x02 + ((-1) * x12)) ≤ 0) ∨ ((t + ((-1) * x02) + x12) ≥ 1) ∨ (¬ (x01 ≤ x02)) ∨ (¬ (x02 ≤ x12)) ∨ (¬ ((x12 - x01) ≥ 1)) ∨ (¬ ((x02 - x01) ≤ (t - 1))) ∨ (¬ ((x12 - x02) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x02) + x12) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th26 t x01 x02 x12
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause404 (t x01 x02 x12 : ℝ) : (((x01 + ((-1) * x12)) ≤ (-1)) ∨ ((x02 + ((-1) * x12)) ≥ 0) ∨ (¬ (x01 ≤ x02)) ∨ (¬ (x02 ≤ x12)) ∨ (¬ ((x12 - x01) ≥ 1)) ∨ (¬ ((x02 - x01) ≤ (t - 1))) ∨ (¬ ((x12 - x02) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x12)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x12)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th26 t x01 x02 x12
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause405 (t x01 x02 x12 : ℝ) : (((x01 + ((-1) * x12)) ≤ (-1)) ∨ ((x01 + ((-1) * x02)) ≥ 0) ∨ (¬ (x01 ≤ x02)) ∨ (¬ (x02 ≤ x12)) ∨ (¬ ((x12 - x01) ≥ 1)) ∨ (¬ ((x02 - x01) ≤ (t - 1))) ∨ (¬ ((x12 - x02) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x12)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x02)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th26 t x01 x02 x12
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause406 (t x01 x02 x12 : ℝ) : (((x01 + ((-1) * x12)) ≥ 1) ∨ ((x01 + ((-1) * x12)) ≤ (-1)) ∨ (¬ (x01 ≤ x02)) ∨ (¬ (x02 ≤ x12)) ∨ (¬ ((x12 - x01) ≥ 1)) ∨ (¬ ((x02 - x01) ≤ (t - 1))) ∨ (¬ ((x12 - x02) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x12)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x12)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th26 t x01 x02 x12
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause407 (t x01 x02 x12 : ℝ) : (((t + ((-1) * x01) + x02) ≥ 1) ∨ ((x01 + ((-1) * x12)) ≤ (-1)) ∨ (¬ (x01 ≤ x02)) ∨ (¬ (x02 ≤ x12)) ∨ (¬ ((x12 - x01) ≥ 1)) ∨ (¬ ((x02 - x01) ≤ (t - 1))) ∨ (¬ ((x12 - x02) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x01) + x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x12)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th26 t x01 x02 x12
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause408 (t x01 x02 x12 : ℝ) : (((x01 + ((-1) * x12)) ≤ (-1)) ∨ ((t + ((-1) * x02) + x12) ≥ 1) ∨ (¬ (x01 ≤ x02)) ∨ (¬ (x02 ≤ x12)) ∨ (¬ ((x12 - x01) ≥ 1)) ∨ (¬ ((x02 - x01) ≤ (t - 1))) ∨ (¬ ((x12 - x02) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x12)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x02) + x12) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th26 t x01 x02 x12
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause411 (t x01 x02 x12 : ℝ) : (((x01 + ((-1) * x12)) ≥ 1) ∨ ((t + x01 + ((-1) * x02)) ≥ 1) ∨ (¬ (x01 ≤ x02)) ∨ (¬ (x02 ≤ x12)) ∨ (¬ ((x12 - x01) ≥ 1)) ∨ (¬ ((x02 - x01) ≤ (t - 1))) ∨ (¬ ((x12 - x02) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x12)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x01 + ((-1) * x02)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th26 t x01 x02 x12
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause414 (t x01 x02 x12 : ℝ) : (((t + x02 + ((-1) * x12)) ≥ 1) ∨ ((x02 + ((-1) * x12)) ≥ 0) ∨ (¬ (x01 ≤ x02)) ∨ (¬ (x02 ≤ x12)) ∨ (¬ ((x12 - x01) ≥ 1)) ∨ (¬ ((x02 - x01) ≤ (t - 1))) ∨ (¬ ((x12 - x02) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x02 + ((-1) * x12)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x12)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th26 t x01 x02 x12
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause415 (t x01 x02 x12 : ℝ) : (((t + x02 + ((-1) * x12)) ≥ 1) ∨ ((x01 + ((-1) * x02)) ≥ 0) ∨ (¬ (x01 ≤ x02)) ∨ (¬ (x02 ≤ x12)) ∨ (¬ ((x12 - x01) ≥ 1)) ∨ (¬ ((x02 - x01) ≤ (t - 1))) ∨ (¬ ((x12 - x02) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x02 + ((-1) * x12)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x02)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th26 t x01 x02 x12
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause416 (t x01 x02 x12 : ℝ) : (((x01 + ((-1) * x12)) ≥ 1) ∨ ((t + x02 + ((-1) * x12)) ≥ 1) ∨ (¬ (x01 ≤ x02)) ∨ (¬ (x02 ≤ x12)) ∨ (¬ ((x12 - x01) ≥ 1)) ∨ (¬ ((x02 - x01) ≤ (t - 1))) ∨ (¬ ((x12 - x02) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x12)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x02 + ((-1) * x12)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th26 t x01 x02 x12
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause419 (t x01 x02 x12 : ℝ) : (((x01 + ((-1) * x02)) ≤ 0) ∨ ((x02 + ((-1) * x12)) ≥ 0) ∨ (¬ (x12 ≤ x02)) ∨ (¬ (x02 ≤ x01)) ∨ (¬ ((x01 - x12) ≥ 1)) ∨ (¬ ((x01 - x02) ≤ (t - 1))) ∨ (¬ ((x02 - x12) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x12)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th26 t x01 x02 x12
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause421 (t x01 x02 x12 : ℝ) : (((x01 + ((-1) * x12)) ≥ 1) ∨ ((x01 + ((-1) * x02)) ≤ 0) ∨ (¬ (x12 ≤ x02)) ∨ (¬ (x02 ≤ x01)) ∨ (¬ ((x01 - x12) ≥ 1)) ∨ (¬ ((x01 - x02) ≤ (t - 1))) ∨ (¬ ((x02 - x12) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x12)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th26 t x01 x02 x12
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause425 (t x01 x02 x12 : ℝ) : (((x02 + ((-1) * x12)) ≤ 0) ∨ ((x01 + ((-1) * x02)) ≥ 0) ∨ (¬ (x12 ≤ x02)) ∨ (¬ (x02 ≤ x01)) ∨ (¬ ((x01 - x12) ≥ 1)) ∨ (¬ ((x01 - x02) ≤ (t - 1))) ∨ (¬ ((x02 - x12) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x02)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th26 t x01 x02 x12
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause428 (t x01 x02 x12 : ℝ) : (((x02 + ((-1) * x12)) ≤ 0) ∨ ((t + ((-1) * x02) + x12) ≥ 1) ∨ (¬ (x12 ≤ x02)) ∨ (¬ (x02 ≤ x01)) ∨ (¬ ((x01 - x12) ≥ 1)) ∨ (¬ ((x01 - x02) ≤ (t - 1))) ∨ (¬ ((x02 - x12) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x02) + x12) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th26 t x01 x02 x12
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause429 (t x01 x02 x12 : ℝ) : (((x01 + ((-1) * x12)) ≤ (-1)) ∨ ((x02 + ((-1) * x12)) ≥ 0) ∨ (¬ (x12 ≤ x02)) ∨ (¬ (x02 ≤ x01)) ∨ (¬ ((x01 - x12) ≥ 1)) ∨ (¬ ((x01 - x02) ≤ (t - 1))) ∨ (¬ ((x02 - x12) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x12)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x12)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th26 t x01 x02 x12
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause430 (t x01 x02 x12 : ℝ) : (((x01 + ((-1) * x12)) ≤ (-1)) ∨ ((x01 + ((-1) * x02)) ≥ 0) ∨ (¬ (x12 ≤ x02)) ∨ (¬ (x02 ≤ x01)) ∨ (¬ ((x01 - x12) ≥ 1)) ∨ (¬ ((x01 - x02) ≤ (t - 1))) ∨ (¬ ((x02 - x12) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x12)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x02)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th26 t x01 x02 x12
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause431 (t x01 x02 x12 : ℝ) : (((x01 + ((-1) * x12)) ≥ 1) ∨ ((x01 + ((-1) * x12)) ≤ (-1)) ∨ (¬ (x12 ≤ x02)) ∨ (¬ (x02 ≤ x01)) ∨ (¬ ((x01 - x12) ≥ 1)) ∨ (¬ ((x01 - x02) ≤ (t - 1))) ∨ (¬ ((x02 - x12) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x12)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x12)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th26 t x01 x02 x12
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause432 (t x01 x02 x12 : ℝ) : (((t + ((-1) * x01) + x02) ≥ 1) ∨ ((x01 + ((-1) * x12)) ≤ (-1)) ∨ (¬ (x12 ≤ x02)) ∨ (¬ (x02 ≤ x01)) ∨ (¬ ((x01 - x12) ≥ 1)) ∨ (¬ ((x01 - x02) ≤ (t - 1))) ∨ (¬ ((x02 - x12) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x01) + x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x12)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th26 t x01 x02 x12
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause433 (t x01 x02 x12 : ℝ) : (((x01 + ((-1) * x12)) ≤ (-1)) ∨ ((t + ((-1) * x02) + x12) ≥ 1) ∨ (¬ (x12 ≤ x02)) ∨ (¬ (x02 ≤ x01)) ∨ (¬ ((x01 - x12) ≥ 1)) ∨ (¬ ((x01 - x02) ≤ (t - 1))) ∨ (¬ ((x02 - x12) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x12)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x02) + x12) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th26 t x01 x02 x12
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause436 (t x01 x02 x12 : ℝ) : (((x01 + ((-1) * x12)) ≥ 1) ∨ ((t + x01 + ((-1) * x02)) ≥ 1) ∨ (¬ (x12 ≤ x02)) ∨ (¬ (x02 ≤ x01)) ∨ (¬ ((x01 - x12) ≥ 1)) ∨ (¬ ((x01 - x02) ≤ (t - 1))) ∨ (¬ ((x02 - x12) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x12)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x01 + ((-1) * x02)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th26 t x01 x02 x12
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause441 (t x01 x02 x12 : ℝ) : (((x01 + ((-1) * x12)) ≥ 1) ∨ ((t + x02 + ((-1) * x12)) ≥ 1) ∨ (¬ (x12 ≤ x02)) ∨ (¬ (x02 ≤ x01)) ∨ (¬ ((x01 - x12) ≥ 1)) ∨ (¬ ((x01 - x02) ≤ (t - 1))) ∨ (¬ ((x02 - x12) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x12)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x02 + ((-1) * x12)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th26 t x01 x02 x12
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause494 (t x01 x02 x12 : ℝ) (h : (((x01 ≤ x02) ∧ (x02 ≤ x12) ∧ ((x12 - x01) ≥ 1) ∧ ((x02 - x01) ≤ (t - 1)) ∧ ((x12 - x02) ≤ (t - 1))) ∨ ((x12 ≤ x02) ∧ (x02 ≤ x01) ∧ ((x01 - x12) ≥ 1) ∧ ((x01 - x02) ≤ (t - 1)) ∧ ((x02 - x12) ≤ (t - 1))))) : ((x01 ≤ x02) ∨ (x12 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x02) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x12 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause495 (t x01 x02 x12 : ℝ) (h : (((x01 ≤ x02) ∧ (x02 ≤ x12) ∧ ((x12 - x01) ≥ 1) ∧ ((x02 - x01) ≤ (t - 1)) ∧ ((x12 - x02) ≤ (t - 1))) ∨ ((x12 ≤ x02) ∧ (x02 ≤ x01) ∧ ((x01 - x12) ≥ 1) ∧ ((x01 - x02) ≤ (t - 1)) ∧ ((x02 - x12) ≤ (t - 1))))) : ((x01 ≤ x02) ∨ (x02 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x02) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x02 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause496 (t x01 x02 x12 : ℝ) (h : (((x01 ≤ x02) ∧ (x02 ≤ x12) ∧ ((x12 - x01) ≥ 1) ∧ ((x02 - x01) ≤ (t - 1)) ∧ ((x12 - x02) ≤ (t - 1))) ∨ ((x12 ≤ x02) ∧ (x02 ≤ x01) ∧ ((x01 - x12) ≥ 1) ∧ ((x01 - x02) ≤ (t - 1)) ∧ ((x02 - x12) ≤ (t - 1))))) : ((x01 ≤ x02) ∨ ((x01 - x12) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x02) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x12) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause497 (t x01 x02 x12 : ℝ) (h : (((x01 ≤ x02) ∧ (x02 ≤ x12) ∧ ((x12 - x01) ≥ 1) ∧ ((x02 - x01) ≤ (t - 1)) ∧ ((x12 - x02) ≤ (t - 1))) ∨ ((x12 ≤ x02) ∧ (x02 ≤ x01) ∧ ((x01 - x12) ≥ 1) ∧ ((x01 - x02) ≤ (t - 1)) ∧ ((x02 - x12) ≤ (t - 1))))) : ((x01 ≤ x02) ∨ ((x01 - x02) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x02) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x02) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause498 (t x01 x02 x12 : ℝ) (h : (((x01 ≤ x02) ∧ (x02 ≤ x12) ∧ ((x12 - x01) ≥ 1) ∧ ((x02 - x01) ≤ (t - 1)) ∧ ((x12 - x02) ≤ (t - 1))) ∨ ((x12 ≤ x02) ∧ (x02 ≤ x01) ∧ ((x01 - x12) ≥ 1) ∧ ((x01 - x02) ≤ (t - 1)) ∧ ((x02 - x12) ≤ (t - 1))))) : ((x01 ≤ x02) ∨ ((x02 - x12) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x02) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x12) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause499 (t x01 x02 x12 : ℝ) (h : (((x01 ≤ x02) ∧ (x02 ≤ x12) ∧ ((x12 - x01) ≥ 1) ∧ ((x02 - x01) ≤ (t - 1)) ∧ ((x12 - x02) ≤ (t - 1))) ∨ ((x12 ≤ x02) ∧ (x02 ≤ x01) ∧ ((x01 - x12) ≥ 1) ∧ ((x01 - x02) ≤ (t - 1)) ∧ ((x02 - x12) ≤ (t - 1))))) : ((x02 ≤ x12) ∨ (x12 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x12) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x12 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause500 (t x01 x02 x12 : ℝ) (h : (((x01 ≤ x02) ∧ (x02 ≤ x12) ∧ ((x12 - x01) ≥ 1) ∧ ((x02 - x01) ≤ (t - 1)) ∧ ((x12 - x02) ≤ (t - 1))) ∨ ((x12 ≤ x02) ∧ (x02 ≤ x01) ∧ ((x01 - x12) ≥ 1) ∧ ((x01 - x02) ≤ (t - 1)) ∧ ((x02 - x12) ≤ (t - 1))))) : ((x02 ≤ x12) ∨ (x02 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x12) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x02 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause501 (t x01 x02 x12 : ℝ) (h : (((x01 ≤ x02) ∧ (x02 ≤ x12) ∧ ((x12 - x01) ≥ 1) ∧ ((x02 - x01) ≤ (t - 1)) ∧ ((x12 - x02) ≤ (t - 1))) ∨ ((x12 ≤ x02) ∧ (x02 ≤ x01) ∧ ((x01 - x12) ≥ 1) ∧ ((x01 - x02) ≤ (t - 1)) ∧ ((x02 - x12) ≤ (t - 1))))) : ((x02 ≤ x12) ∨ ((x01 - x12) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x12) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x12) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause502 (t x01 x02 x12 : ℝ) (h : (((x01 ≤ x02) ∧ (x02 ≤ x12) ∧ ((x12 - x01) ≥ 1) ∧ ((x02 - x01) ≤ (t - 1)) ∧ ((x12 - x02) ≤ (t - 1))) ∨ ((x12 ≤ x02) ∧ (x02 ≤ x01) ∧ ((x01 - x12) ≥ 1) ∧ ((x01 - x02) ≤ (t - 1)) ∧ ((x02 - x12) ≤ (t - 1))))) : ((x02 ≤ x12) ∨ ((x01 - x02) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x12) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x02) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause503 (t x01 x02 x12 : ℝ) (h : (((x01 ≤ x02) ∧ (x02 ≤ x12) ∧ ((x12 - x01) ≥ 1) ∧ ((x02 - x01) ≤ (t - 1)) ∧ ((x12 - x02) ≤ (t - 1))) ∨ ((x12 ≤ x02) ∧ (x02 ≤ x01) ∧ ((x01 - x12) ≥ 1) ∧ ((x01 - x02) ≤ (t - 1)) ∧ ((x02 - x12) ≤ (t - 1))))) : ((x02 ≤ x12) ∨ ((x02 - x12) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x12) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x12) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause504 (t x01 x02 x12 : ℝ) (h : (((x01 ≤ x02) ∧ (x02 ≤ x12) ∧ ((x12 - x01) ≥ 1) ∧ ((x02 - x01) ≤ (t - 1)) ∧ ((x12 - x02) ≤ (t - 1))) ∨ ((x12 ≤ x02) ∧ (x02 ≤ x01) ∧ ((x01 - x12) ≥ 1) ∧ ((x01 - x02) ≤ (t - 1)) ∧ ((x02 - x12) ≤ (t - 1))))) : (((x12 - x01) ≥ 1) ∨ (x12 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x12 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause505 (t x01 x02 x12 : ℝ) (h : (((x01 ≤ x02) ∧ (x02 ≤ x12) ∧ ((x12 - x01) ≥ 1) ∧ ((x02 - x01) ≤ (t - 1)) ∧ ((x12 - x02) ≤ (t - 1))) ∨ ((x12 ≤ x02) ∧ (x02 ≤ x01) ∧ ((x01 - x12) ≥ 1) ∧ ((x01 - x02) ≤ (t - 1)) ∧ ((x02 - x12) ≤ (t - 1))))) : (((x12 - x01) ≥ 1) ∨ (x02 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x02 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause506 (t x01 x02 x12 : ℝ) (h : (((x01 ≤ x02) ∧ (x02 ≤ x12) ∧ ((x12 - x01) ≥ 1) ∧ ((x02 - x01) ≤ (t - 1)) ∧ ((x12 - x02) ≤ (t - 1))) ∨ ((x12 ≤ x02) ∧ (x02 ≤ x01) ∧ ((x01 - x12) ≥ 1) ∧ ((x01 - x02) ≤ (t - 1)) ∧ ((x02 - x12) ≤ (t - 1))))) : (((x12 - x01) ≥ 1) ∨ ((x01 - x12) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x12) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause507 (t x01 x02 x12 : ℝ) (h : (((x01 ≤ x02) ∧ (x02 ≤ x12) ∧ ((x12 - x01) ≥ 1) ∧ ((x02 - x01) ≤ (t - 1)) ∧ ((x12 - x02) ≤ (t - 1))) ∨ ((x12 ≤ x02) ∧ (x02 ≤ x01) ∧ ((x01 - x12) ≥ 1) ∧ ((x01 - x02) ≤ (t - 1)) ∧ ((x02 - x12) ≤ (t - 1))))) : (((x12 - x01) ≥ 1) ∨ ((x01 - x02) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x02) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause508 (t x01 x02 x12 : ℝ) (h : (((x01 ≤ x02) ∧ (x02 ≤ x12) ∧ ((x12 - x01) ≥ 1) ∧ ((x02 - x01) ≤ (t - 1)) ∧ ((x12 - x02) ≤ (t - 1))) ∨ ((x12 ≤ x02) ∧ (x02 ≤ x01) ∧ ((x01 - x12) ≥ 1) ∧ ((x01 - x02) ≤ (t - 1)) ∧ ((x02 - x12) ≤ (t - 1))))) : (((x12 - x01) ≥ 1) ∨ ((x02 - x12) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x12) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause509 (t x01 x02 x12 : ℝ) (h : (((x01 ≤ x02) ∧ (x02 ≤ x12) ∧ ((x12 - x01) ≥ 1) ∧ ((x02 - x01) ≤ (t - 1)) ∧ ((x12 - x02) ≤ (t - 1))) ∨ ((x12 ≤ x02) ∧ (x02 ≤ x01) ∧ ((x01 - x12) ≥ 1) ∧ ((x01 - x02) ≤ (t - 1)) ∧ ((x02 - x12) ≤ (t - 1))))) : (((x02 - x01) ≤ (t - 1)) ∨ (x12 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x12 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause510 (t x01 x02 x12 : ℝ) (h : (((x01 ≤ x02) ∧ (x02 ≤ x12) ∧ ((x12 - x01) ≥ 1) ∧ ((x02 - x01) ≤ (t - 1)) ∧ ((x12 - x02) ≤ (t - 1))) ∨ ((x12 ≤ x02) ∧ (x02 ≤ x01) ∧ ((x01 - x12) ≥ 1) ∧ ((x01 - x02) ≤ (t - 1)) ∧ ((x02 - x12) ≤ (t - 1))))) : (((x02 - x01) ≤ (t - 1)) ∨ (x02 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x02 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause511 (t x01 x02 x12 : ℝ) (h : (((x01 ≤ x02) ∧ (x02 ≤ x12) ∧ ((x12 - x01) ≥ 1) ∧ ((x02 - x01) ≤ (t - 1)) ∧ ((x12 - x02) ≤ (t - 1))) ∨ ((x12 ≤ x02) ∧ (x02 ≤ x01) ∧ ((x01 - x12) ≥ 1) ∧ ((x01 - x02) ≤ (t - 1)) ∧ ((x02 - x12) ≤ (t - 1))))) : (((x02 - x01) ≤ (t - 1)) ∨ ((x01 - x12) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x12) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause512 (t x01 x02 x12 : ℝ) (h : (((x01 ≤ x02) ∧ (x02 ≤ x12) ∧ ((x12 - x01) ≥ 1) ∧ ((x02 - x01) ≤ (t - 1)) ∧ ((x12 - x02) ≤ (t - 1))) ∨ ((x12 ≤ x02) ∧ (x02 ≤ x01) ∧ ((x01 - x12) ≥ 1) ∧ ((x01 - x02) ≤ (t - 1)) ∧ ((x02 - x12) ≤ (t - 1))))) : (((x02 - x01) ≤ (t - 1)) ∨ ((x01 - x02) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x02) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause513 (t x01 x02 x12 : ℝ) (h : (((x01 ≤ x02) ∧ (x02 ≤ x12) ∧ ((x12 - x01) ≥ 1) ∧ ((x02 - x01) ≤ (t - 1)) ∧ ((x12 - x02) ≤ (t - 1))) ∨ ((x12 ≤ x02) ∧ (x02 ≤ x01) ∧ ((x01 - x12) ≥ 1) ∧ ((x01 - x02) ≤ (t - 1)) ∧ ((x02 - x12) ≤ (t - 1))))) : (((x02 - x01) ≤ (t - 1)) ∨ ((x02 - x12) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x12) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause514 (t x01 x02 x12 : ℝ) (h : (((x01 ≤ x02) ∧ (x02 ≤ x12) ∧ ((x12 - x01) ≥ 1) ∧ ((x02 - x01) ≤ (t - 1)) ∧ ((x12 - x02) ≤ (t - 1))) ∨ ((x12 ≤ x02) ∧ (x02 ≤ x01) ∧ ((x01 - x12) ≥ 1) ∧ ((x01 - x02) ≤ (t - 1)) ∧ ((x02 - x12) ≤ (t - 1))))) : (((x12 - x02) ≤ (t - 1)) ∨ (x12 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x12 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause515 (t x01 x02 x12 : ℝ) (h : (((x01 ≤ x02) ∧ (x02 ≤ x12) ∧ ((x12 - x01) ≥ 1) ∧ ((x02 - x01) ≤ (t - 1)) ∧ ((x12 - x02) ≤ (t - 1))) ∨ ((x12 ≤ x02) ∧ (x02 ≤ x01) ∧ ((x01 - x12) ≥ 1) ∧ ((x01 - x02) ≤ (t - 1)) ∧ ((x02 - x12) ≤ (t - 1))))) : (((x12 - x02) ≤ (t - 1)) ∨ (x02 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x02 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause516 (t x01 x02 x12 : ℝ) (h : (((x01 ≤ x02) ∧ (x02 ≤ x12) ∧ ((x12 - x01) ≥ 1) ∧ ((x02 - x01) ≤ (t - 1)) ∧ ((x12 - x02) ≤ (t - 1))) ∨ ((x12 ≤ x02) ∧ (x02 ≤ x01) ∧ ((x01 - x12) ≥ 1) ∧ ((x01 - x02) ≤ (t - 1)) ∧ ((x02 - x12) ≤ (t - 1))))) : (((x12 - x02) ≤ (t - 1)) ∨ ((x01 - x12) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x12) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause517 (t x01 x02 x12 : ℝ) (h : (((x01 ≤ x02) ∧ (x02 ≤ x12) ∧ ((x12 - x01) ≥ 1) ∧ ((x02 - x01) ≤ (t - 1)) ∧ ((x12 - x02) ≤ (t - 1))) ∨ ((x12 ≤ x02) ∧ (x02 ≤ x01) ∧ ((x01 - x12) ≥ 1) ∧ ((x01 - x02) ≤ (t - 1)) ∧ ((x02 - x12) ≤ (t - 1))))) : (((x12 - x02) ≤ (t - 1)) ∨ ((x01 - x02) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x02) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause518 (t x01 x02 x12 : ℝ) (h : (((x01 ≤ x02) ∧ (x02 ≤ x12) ∧ ((x12 - x01) ≥ 1) ∧ ((x02 - x01) ≤ (t - 1)) ∧ ((x12 - x02) ≤ (t - 1))) ∨ ((x12 ≤ x02) ∧ (x02 ≤ x01) ∧ ((x01 - x12) ≥ 1) ∧ ((x01 - x02) ≤ (t - 1)) ∧ ((x02 - x12) ≤ (t - 1))))) : (((x12 - x02) ≤ (t - 1)) ∨ ((x02 - x12) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x12) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause519 (x34 x45 : ℝ) : ((¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th28 x34 x45
  exact (fun hh => (Or.elim hh (fun hh => hh u0) (fun zz => ((fun hh => hh u1) zz)))) h

theorem clause520 (t x34 x35 x45 : ℝ) : (((x34 + ((-1) * x35)) ≤ 0) ∨ ((x35 + ((-1) * x45)) ≥ 0) ∨ (¬ (x34 ≤ x35)) ∨ (¬ (x35 ≤ x45)) ∨ (¬ ((x45 - x34) ≥ 1)) ∨ (¬ ((x35 - x34) ≤ (t - 1))) ∨ (¬ ((x45 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x45)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th30 t x34 x35 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause522 (t x34 x35 x45 : ℝ) : (((x34 + ((-1) * x45)) ≥ 1) ∨ ((x34 + ((-1) * x35)) ≤ 0) ∨ (¬ (x34 ≤ x35)) ∨ (¬ (x35 ≤ x45)) ∨ (¬ ((x45 - x34) ≥ 1)) ∨ (¬ ((x35 - x34) ≤ (t - 1))) ∨ (¬ ((x45 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th30 t x34 x35 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause523 (t x34 x35 x45 : ℝ) : (((x34 + ((-1) * x35)) ≤ 0) ∨ ((t + ((-1) * x34) + x35) ≥ 1) ∨ (¬ (x34 ≤ x35)) ∨ (¬ (x35 ≤ x45)) ∨ (¬ ((x45 - x34) ≥ 1)) ∨ (¬ ((x35 - x34) ≤ (t - 1))) ∨ (¬ ((x45 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x34) + x35) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th30 t x34 x35 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause526 (t x34 x35 x45 : ℝ) : (((x35 + ((-1) * x45)) ≤ 0) ∨ ((x34 + ((-1) * x35)) ≥ 0) ∨ (¬ (x34 ≤ x35)) ∨ (¬ (x35 ≤ x45)) ∨ (¬ ((x45 - x34) ≥ 1)) ∨ (¬ ((x35 - x34) ≤ (t - 1))) ∨ (¬ ((x45 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x35)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th30 t x34 x35 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause527 (t x34 x35 x45 : ℝ) : (((x34 + ((-1) * x45)) ≥ 1) ∨ ((x35 + ((-1) * x45)) ≤ 0) ∨ (¬ (x34 ≤ x35)) ∨ (¬ (x35 ≤ x45)) ∨ (¬ ((x45 - x34) ≥ 1)) ∨ (¬ ((x35 - x34) ≤ (t - 1))) ∨ (¬ ((x45 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th30 t x34 x35 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause529 (t x34 x35 x45 : ℝ) : (((x35 + ((-1) * x45)) ≤ 0) ∨ ((t + ((-1) * x35) + x45) ≥ 1) ∨ (¬ (x34 ≤ x35)) ∨ (¬ (x35 ≤ x45)) ∨ (¬ ((x45 - x34) ≥ 1)) ∨ (¬ ((x35 - x34) ≤ (t - 1))) ∨ (¬ ((x45 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x35) + x45) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th30 t x34 x35 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause530 (t x34 x35 x45 : ℝ) : (((x34 + ((-1) * x45)) ≤ (-1)) ∨ ((x35 + ((-1) * x45)) ≥ 0) ∨ (¬ (x34 ≤ x35)) ∨ (¬ (x35 ≤ x45)) ∨ (¬ ((x45 - x34) ≥ 1)) ∨ (¬ ((x35 - x34) ≤ (t - 1))) ∨ (¬ ((x45 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x45)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th30 t x34 x35 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause531 (t x34 x35 x45 : ℝ) : (((x34 + ((-1) * x45)) ≤ (-1)) ∨ ((x34 + ((-1) * x35)) ≥ 0) ∨ (¬ (x34 ≤ x35)) ∨ (¬ (x35 ≤ x45)) ∨ (¬ ((x45 - x34) ≥ 1)) ∨ (¬ ((x35 - x34) ≤ (t - 1))) ∨ (¬ ((x45 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x35)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th30 t x34 x35 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause532 (t x34 x35 x45 : ℝ) : (((x34 + ((-1) * x45)) ≤ (-1)) ∨ ((x34 + ((-1) * x45)) ≥ 1) ∨ (¬ (x34 ≤ x35)) ∨ (¬ (x35 ≤ x45)) ∨ (¬ ((x45 - x34) ≥ 1)) ∨ (¬ ((x35 - x34) ≤ (t - 1))) ∨ (¬ ((x45 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th30 t x34 x35 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause537 (t x34 x35 x45 : ℝ) : (((x34 + ((-1) * x45)) ≥ 1) ∨ ((t + x34 + ((-1) * x35)) ≥ 1) ∨ (¬ (x34 ≤ x35)) ∨ (¬ (x35 ≤ x45)) ∨ (¬ ((x45 - x34) ≥ 1)) ∨ (¬ ((x35 - x34) ≤ (t - 1))) ∨ (¬ ((x45 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x34 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th30 t x34 x35 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause540 (t x34 x35 x45 : ℝ) : (((t + x35 + ((-1) * x45)) ≥ 1) ∨ ((x35 + ((-1) * x45)) ≥ 0) ∨ (¬ (x34 ≤ x35)) ∨ (¬ (x35 ≤ x45)) ∨ (¬ ((x45 - x34) ≥ 1)) ∨ (¬ ((x35 - x34) ≤ (t - 1))) ∨ (¬ ((x45 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x35 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x45)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th30 t x34 x35 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause542 (t x34 x35 x45 : ℝ) : (((x34 + ((-1) * x45)) ≥ 1) ∨ ((t + x35 + ((-1) * x45)) ≥ 1) ∨ (¬ (x34 ≤ x35)) ∨ (¬ (x35 ≤ x45)) ∨ (¬ ((x45 - x34) ≥ 1)) ∨ (¬ ((x35 - x34) ≤ (t - 1))) ∨ (¬ ((x45 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x35 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th30 t x34 x35 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause547 (t x34 x35 x45 : ℝ) : (((x34 + ((-1) * x45)) ≥ 1) ∨ ((x34 + ((-1) * x35)) ≤ 0) ∨ (¬ (x45 ≤ x35)) ∨ (¬ (x35 ≤ x34)) ∨ (¬ ((x34 - x45) ≥ 1)) ∨ (¬ ((x34 - x35) ≤ (t - 1))) ∨ (¬ ((x35 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th30 t x34 x35 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause548 (t x34 x35 x45 : ℝ) : (((x34 + ((-1) * x35)) ≤ 0) ∨ ((t + ((-1) * x34) + x35) ≥ 1) ∨ (¬ (x45 ≤ x35)) ∨ (¬ (x35 ≤ x34)) ∨ (¬ ((x34 - x45) ≥ 1)) ∨ (¬ ((x34 - x35) ≤ (t - 1))) ∨ (¬ ((x35 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x34) + x35) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th30 t x34 x35 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause551 (t x34 x35 x45 : ℝ) : (((x35 + ((-1) * x45)) ≤ 0) ∨ ((x34 + ((-1) * x35)) ≥ 0) ∨ (¬ (x45 ≤ x35)) ∨ (¬ (x35 ≤ x34)) ∨ (¬ ((x34 - x45) ≥ 1)) ∨ (¬ ((x34 - x35) ≤ (t - 1))) ∨ (¬ ((x35 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x35)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th30 t x34 x35 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause552 (t x34 x35 x45 : ℝ) : (((x34 + ((-1) * x45)) ≥ 1) ∨ ((x35 + ((-1) * x45)) ≤ 0) ∨ (¬ (x45 ≤ x35)) ∨ (¬ (x35 ≤ x34)) ∨ (¬ ((x34 - x45) ≥ 1)) ∨ (¬ ((x34 - x35) ≤ (t - 1))) ∨ (¬ ((x35 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th30 t x34 x35 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause554 (t x34 x35 x45 : ℝ) : (((x35 + ((-1) * x45)) ≤ 0) ∨ ((t + ((-1) * x35) + x45) ≥ 1) ∨ (¬ (x45 ≤ x35)) ∨ (¬ (x35 ≤ x34)) ∨ (¬ ((x34 - x45) ≥ 1)) ∨ (¬ ((x34 - x35) ≤ (t - 1))) ∨ (¬ ((x35 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x35) + x45) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th30 t x34 x35 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause555 (t x34 x35 x45 : ℝ) : (((x34 + ((-1) * x45)) ≤ (-1)) ∨ ((x35 + ((-1) * x45)) ≥ 0) ∨ (¬ (x45 ≤ x35)) ∨ (¬ (x35 ≤ x34)) ∨ (¬ ((x34 - x45) ≥ 1)) ∨ (¬ ((x34 - x35) ≤ (t - 1))) ∨ (¬ ((x35 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x45)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th30 t x34 x35 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause556 (t x34 x35 x45 : ℝ) : (((x34 + ((-1) * x45)) ≤ (-1)) ∨ ((x34 + ((-1) * x35)) ≥ 0) ∨ (¬ (x45 ≤ x35)) ∨ (¬ (x35 ≤ x34)) ∨ (¬ ((x34 - x45) ≥ 1)) ∨ (¬ ((x34 - x35) ≤ (t - 1))) ∨ (¬ ((x35 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x35)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th30 t x34 x35 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause557 (t x34 x35 x45 : ℝ) : (((x34 + ((-1) * x45)) ≤ (-1)) ∨ ((x34 + ((-1) * x45)) ≥ 1) ∨ (¬ (x45 ≤ x35)) ∨ (¬ (x35 ≤ x34)) ∨ (¬ ((x34 - x45) ≥ 1)) ∨ (¬ ((x34 - x35) ≤ (t - 1))) ∨ (¬ ((x35 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th30 t x34 x35 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause562 (t x34 x35 x45 : ℝ) : (((x34 + ((-1) * x45)) ≥ 1) ∨ ((t + x34 + ((-1) * x35)) ≥ 1) ∨ (¬ (x45 ≤ x35)) ∨ (¬ (x35 ≤ x34)) ∨ (¬ ((x34 - x45) ≥ 1)) ∨ (¬ ((x34 - x35) ≤ (t - 1))) ∨ (¬ ((x35 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x34 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th30 t x34 x35 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause567 (t x34 x35 x45 : ℝ) : (((x34 + ((-1) * x45)) ≥ 1) ∨ ((t + x35 + ((-1) * x45)) ≥ 1) ∨ (¬ (x45 ≤ x35)) ∨ (¬ (x35 ≤ x34)) ∨ (¬ ((x34 - x45) ≥ 1)) ∨ (¬ ((x34 - x35) ≤ (t - 1))) ∨ (¬ ((x35 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x35 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th30 t x34 x35 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause620 (t x34 x35 x45 : ℝ) (h : (((x34 ≤ x35) ∧ (x35 ≤ x45) ∧ ((x45 - x34) ≥ 1) ∧ ((x35 - x34) ≤ (t - 1)) ∧ ((x45 - x35) ≤ (t - 1))) ∨ ((x45 ≤ x35) ∧ (x35 ≤ x34) ∧ ((x34 - x45) ≥ 1) ∧ ((x34 - x35) ≤ (t - 1)) ∧ ((x35 - x45) ≤ (t - 1))))) : ((x34 ≤ x35) ∨ (x45 ≤ x35)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x34 ≤ x35) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x45 ≤ x35) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause621 (t x34 x35 x45 : ℝ) (h : (((x34 ≤ x35) ∧ (x35 ≤ x45) ∧ ((x45 - x34) ≥ 1) ∧ ((x35 - x34) ≤ (t - 1)) ∧ ((x45 - x35) ≤ (t - 1))) ∨ ((x45 ≤ x35) ∧ (x35 ≤ x34) ∧ ((x34 - x45) ≥ 1) ∧ ((x34 - x35) ≤ (t - 1)) ∧ ((x35 - x45) ≤ (t - 1))))) : ((x34 ≤ x35) ∨ (x35 ≤ x34)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x34 ≤ x35) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x35 ≤ x34) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause622 (t x34 x35 x45 : ℝ) (h : (((x34 ≤ x35) ∧ (x35 ≤ x45) ∧ ((x45 - x34) ≥ 1) ∧ ((x35 - x34) ≤ (t - 1)) ∧ ((x45 - x35) ≤ (t - 1))) ∨ ((x45 ≤ x35) ∧ (x35 ≤ x34) ∧ ((x34 - x45) ≥ 1) ∧ ((x34 - x35) ≤ (t - 1)) ∧ ((x35 - x45) ≤ (t - 1))))) : ((x34 ≤ x35) ∨ ((x34 - x45) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x34 ≤ x35) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x45) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause623 (t x34 x35 x45 : ℝ) (h : (((x34 ≤ x35) ∧ (x35 ≤ x45) ∧ ((x45 - x34) ≥ 1) ∧ ((x35 - x34) ≤ (t - 1)) ∧ ((x45 - x35) ≤ (t - 1))) ∨ ((x45 ≤ x35) ∧ (x35 ≤ x34) ∧ ((x34 - x45) ≥ 1) ∧ ((x34 - x35) ≤ (t - 1)) ∧ ((x35 - x45) ≤ (t - 1))))) : ((x34 ≤ x35) ∨ ((x34 - x35) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x34 ≤ x35) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x35) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause624 (t x34 x35 x45 : ℝ) (h : (((x34 ≤ x35) ∧ (x35 ≤ x45) ∧ ((x45 - x34) ≥ 1) ∧ ((x35 - x34) ≤ (t - 1)) ∧ ((x45 - x35) ≤ (t - 1))) ∨ ((x45 ≤ x35) ∧ (x35 ≤ x34) ∧ ((x34 - x45) ≥ 1) ∧ ((x34 - x35) ≤ (t - 1)) ∧ ((x35 - x45) ≤ (t - 1))))) : ((x34 ≤ x35) ∨ ((x35 - x45) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x34 ≤ x35) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x45) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause625 (t x34 x35 x45 : ℝ) (h : (((x34 ≤ x35) ∧ (x35 ≤ x45) ∧ ((x45 - x34) ≥ 1) ∧ ((x35 - x34) ≤ (t - 1)) ∧ ((x45 - x35) ≤ (t - 1))) ∨ ((x45 ≤ x35) ∧ (x35 ≤ x34) ∧ ((x34 - x45) ≥ 1) ∧ ((x34 - x35) ≤ (t - 1)) ∧ ((x35 - x45) ≤ (t - 1))))) : ((x35 ≤ x45) ∨ (x45 ≤ x35)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x35 ≤ x45) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x45 ≤ x35) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause626 (t x34 x35 x45 : ℝ) (h : (((x34 ≤ x35) ∧ (x35 ≤ x45) ∧ ((x45 - x34) ≥ 1) ∧ ((x35 - x34) ≤ (t - 1)) ∧ ((x45 - x35) ≤ (t - 1))) ∨ ((x45 ≤ x35) ∧ (x35 ≤ x34) ∧ ((x34 - x45) ≥ 1) ∧ ((x34 - x35) ≤ (t - 1)) ∧ ((x35 - x45) ≤ (t - 1))))) : ((x35 ≤ x45) ∨ (x35 ≤ x34)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x35 ≤ x45) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x35 ≤ x34) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause627 (t x34 x35 x45 : ℝ) (h : (((x34 ≤ x35) ∧ (x35 ≤ x45) ∧ ((x45 - x34) ≥ 1) ∧ ((x35 - x34) ≤ (t - 1)) ∧ ((x45 - x35) ≤ (t - 1))) ∨ ((x45 ≤ x35) ∧ (x35 ≤ x34) ∧ ((x34 - x45) ≥ 1) ∧ ((x34 - x35) ≤ (t - 1)) ∧ ((x35 - x45) ≤ (t - 1))))) : ((x35 ≤ x45) ∨ ((x34 - x45) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x35 ≤ x45) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x45) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause628 (t x34 x35 x45 : ℝ) (h : (((x34 ≤ x35) ∧ (x35 ≤ x45) ∧ ((x45 - x34) ≥ 1) ∧ ((x35 - x34) ≤ (t - 1)) ∧ ((x45 - x35) ≤ (t - 1))) ∨ ((x45 ≤ x35) ∧ (x35 ≤ x34) ∧ ((x34 - x45) ≥ 1) ∧ ((x34 - x35) ≤ (t - 1)) ∧ ((x35 - x45) ≤ (t - 1))))) : ((x35 ≤ x45) ∨ ((x34 - x35) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x35 ≤ x45) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x35) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause629 (t x34 x35 x45 : ℝ) (h : (((x34 ≤ x35) ∧ (x35 ≤ x45) ∧ ((x45 - x34) ≥ 1) ∧ ((x35 - x34) ≤ (t - 1)) ∧ ((x45 - x35) ≤ (t - 1))) ∨ ((x45 ≤ x35) ∧ (x35 ≤ x34) ∧ ((x34 - x45) ≥ 1) ∧ ((x34 - x35) ≤ (t - 1)) ∧ ((x35 - x45) ≤ (t - 1))))) : ((x35 ≤ x45) ∨ ((x35 - x45) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x35 ≤ x45) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x45) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause630 (t x34 x35 x45 : ℝ) (h : (((x34 ≤ x35) ∧ (x35 ≤ x45) ∧ ((x45 - x34) ≥ 1) ∧ ((x35 - x34) ≤ (t - 1)) ∧ ((x45 - x35) ≤ (t - 1))) ∨ ((x45 ≤ x35) ∧ (x35 ≤ x34) ∧ ((x34 - x45) ≥ 1) ∧ ((x34 - x35) ≤ (t - 1)) ∧ ((x35 - x45) ≤ (t - 1))))) : (((x45 - x34) ≥ 1) ∨ (x45 ≤ x35)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x34) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x45 ≤ x35) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause631 (t x34 x35 x45 : ℝ) (h : (((x34 ≤ x35) ∧ (x35 ≤ x45) ∧ ((x45 - x34) ≥ 1) ∧ ((x35 - x34) ≤ (t - 1)) ∧ ((x45 - x35) ≤ (t - 1))) ∨ ((x45 ≤ x35) ∧ (x35 ≤ x34) ∧ ((x34 - x45) ≥ 1) ∧ ((x34 - x35) ≤ (t - 1)) ∧ ((x35 - x45) ≤ (t - 1))))) : (((x45 - x34) ≥ 1) ∨ (x35 ≤ x34)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x34) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x35 ≤ x34) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause632 (t x34 x35 x45 : ℝ) (h : (((x34 ≤ x35) ∧ (x35 ≤ x45) ∧ ((x45 - x34) ≥ 1) ∧ ((x35 - x34) ≤ (t - 1)) ∧ ((x45 - x35) ≤ (t - 1))) ∨ ((x45 ≤ x35) ∧ (x35 ≤ x34) ∧ ((x34 - x45) ≥ 1) ∧ ((x34 - x35) ≤ (t - 1)) ∧ ((x35 - x45) ≤ (t - 1))))) : (((x45 - x34) ≥ 1) ∨ ((x34 - x45) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x34) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x45) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause633 (t x34 x35 x45 : ℝ) (h : (((x34 ≤ x35) ∧ (x35 ≤ x45) ∧ ((x45 - x34) ≥ 1) ∧ ((x35 - x34) ≤ (t - 1)) ∧ ((x45 - x35) ≤ (t - 1))) ∨ ((x45 ≤ x35) ∧ (x35 ≤ x34) ∧ ((x34 - x45) ≥ 1) ∧ ((x34 - x35) ≤ (t - 1)) ∧ ((x35 - x45) ≤ (t - 1))))) : (((x45 - x34) ≥ 1) ∨ ((x34 - x35) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x34) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x35) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause634 (t x34 x35 x45 : ℝ) (h : (((x34 ≤ x35) ∧ (x35 ≤ x45) ∧ ((x45 - x34) ≥ 1) ∧ ((x35 - x34) ≤ (t - 1)) ∧ ((x45 - x35) ≤ (t - 1))) ∨ ((x45 ≤ x35) ∧ (x35 ≤ x34) ∧ ((x34 - x45) ≥ 1) ∧ ((x34 - x35) ≤ (t - 1)) ∧ ((x35 - x45) ≤ (t - 1))))) : (((x45 - x34) ≥ 1) ∨ ((x35 - x45) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x34) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x45) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause635 (t x34 x35 x45 : ℝ) (h : (((x34 ≤ x35) ∧ (x35 ≤ x45) ∧ ((x45 - x34) ≥ 1) ∧ ((x35 - x34) ≤ (t - 1)) ∧ ((x45 - x35) ≤ (t - 1))) ∨ ((x45 ≤ x35) ∧ (x35 ≤ x34) ∧ ((x34 - x45) ≥ 1) ∧ ((x34 - x35) ≤ (t - 1)) ∧ ((x35 - x45) ≤ (t - 1))))) : (((x35 - x34) ≤ (t - 1)) ∨ (x45 ≤ x35)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x34) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x45 ≤ x35) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause636 (t x34 x35 x45 : ℝ) (h : (((x34 ≤ x35) ∧ (x35 ≤ x45) ∧ ((x45 - x34) ≥ 1) ∧ ((x35 - x34) ≤ (t - 1)) ∧ ((x45 - x35) ≤ (t - 1))) ∨ ((x45 ≤ x35) ∧ (x35 ≤ x34) ∧ ((x34 - x45) ≥ 1) ∧ ((x34 - x35) ≤ (t - 1)) ∧ ((x35 - x45) ≤ (t - 1))))) : (((x35 - x34) ≤ (t - 1)) ∨ (x35 ≤ x34)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x34) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x35 ≤ x34) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause637 (t x34 x35 x45 : ℝ) (h : (((x34 ≤ x35) ∧ (x35 ≤ x45) ∧ ((x45 - x34) ≥ 1) ∧ ((x35 - x34) ≤ (t - 1)) ∧ ((x45 - x35) ≤ (t - 1))) ∨ ((x45 ≤ x35) ∧ (x35 ≤ x34) ∧ ((x34 - x45) ≥ 1) ∧ ((x34 - x35) ≤ (t - 1)) ∧ ((x35 - x45) ≤ (t - 1))))) : (((x35 - x34) ≤ (t - 1)) ∨ ((x34 - x45) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x34) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x45) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause638 (t x34 x35 x45 : ℝ) (h : (((x34 ≤ x35) ∧ (x35 ≤ x45) ∧ ((x45 - x34) ≥ 1) ∧ ((x35 - x34) ≤ (t - 1)) ∧ ((x45 - x35) ≤ (t - 1))) ∨ ((x45 ≤ x35) ∧ (x35 ≤ x34) ∧ ((x34 - x45) ≥ 1) ∧ ((x34 - x35) ≤ (t - 1)) ∧ ((x35 - x45) ≤ (t - 1))))) : (((x35 - x34) ≤ (t - 1)) ∨ ((x34 - x35) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x34) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x35) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause639 (t x34 x35 x45 : ℝ) (h : (((x34 ≤ x35) ∧ (x35 ≤ x45) ∧ ((x45 - x34) ≥ 1) ∧ ((x35 - x34) ≤ (t - 1)) ∧ ((x45 - x35) ≤ (t - 1))) ∨ ((x45 ≤ x35) ∧ (x35 ≤ x34) ∧ ((x34 - x45) ≥ 1) ∧ ((x34 - x35) ≤ (t - 1)) ∧ ((x35 - x45) ≤ (t - 1))))) : (((x35 - x34) ≤ (t - 1)) ∨ ((x35 - x45) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x34) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x45) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause640 (t x34 x35 x45 : ℝ) (h : (((x34 ≤ x35) ∧ (x35 ≤ x45) ∧ ((x45 - x34) ≥ 1) ∧ ((x35 - x34) ≤ (t - 1)) ∧ ((x45 - x35) ≤ (t - 1))) ∨ ((x45 ≤ x35) ∧ (x35 ≤ x34) ∧ ((x34 - x45) ≥ 1) ∧ ((x34 - x35) ≤ (t - 1)) ∧ ((x35 - x45) ≤ (t - 1))))) : (((x45 - x35) ≤ (t - 1)) ∨ (x45 ≤ x35)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x35) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x45 ≤ x35) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause641 (t x34 x35 x45 : ℝ) (h : (((x34 ≤ x35) ∧ (x35 ≤ x45) ∧ ((x45 - x34) ≥ 1) ∧ ((x35 - x34) ≤ (t - 1)) ∧ ((x45 - x35) ≤ (t - 1))) ∨ ((x45 ≤ x35) ∧ (x35 ≤ x34) ∧ ((x34 - x45) ≥ 1) ∧ ((x34 - x35) ≤ (t - 1)) ∧ ((x35 - x45) ≤ (t - 1))))) : (((x45 - x35) ≤ (t - 1)) ∨ (x35 ≤ x34)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x35) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x35 ≤ x34) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause642 (t x34 x35 x45 : ℝ) (h : (((x34 ≤ x35) ∧ (x35 ≤ x45) ∧ ((x45 - x34) ≥ 1) ∧ ((x35 - x34) ≤ (t - 1)) ∧ ((x45 - x35) ≤ (t - 1))) ∨ ((x45 ≤ x35) ∧ (x35 ≤ x34) ∧ ((x34 - x45) ≥ 1) ∧ ((x34 - x35) ≤ (t - 1)) ∧ ((x35 - x45) ≤ (t - 1))))) : (((x45 - x35) ≤ (t - 1)) ∨ ((x34 - x45) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x35) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x45) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause643 (t x34 x35 x45 : ℝ) (h : (((x34 ≤ x35) ∧ (x35 ≤ x45) ∧ ((x45 - x34) ≥ 1) ∧ ((x35 - x34) ≤ (t - 1)) ∧ ((x45 - x35) ≤ (t - 1))) ∨ ((x45 ≤ x35) ∧ (x35 ≤ x34) ∧ ((x34 - x45) ≥ 1) ∧ ((x34 - x35) ≤ (t - 1)) ∧ ((x35 - x45) ≤ (t - 1))))) : (((x45 - x35) ≤ (t - 1)) ∨ ((x34 - x35) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x35) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x35) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause644 (t x34 x35 x45 : ℝ) (h : (((x34 ≤ x35) ∧ (x35 ≤ x45) ∧ ((x45 - x34) ≥ 1) ∧ ((x35 - x34) ≤ (t - 1)) ∧ ((x45 - x35) ≤ (t - 1))) ∨ ((x45 ≤ x35) ∧ (x35 ≤ x34) ∧ ((x34 - x45) ≥ 1) ∧ ((x34 - x35) ≤ (t - 1)) ∧ ((x35 - x45) ≤ (t - 1))))) : (((x45 - x35) ≤ (t - 1)) ∨ ((x35 - x45) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x35) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x45) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause645 (x01 x12 : ℝ) : ((¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th32 x01 x12
  exact (fun hh => (Or.elim hh (fun hh => hh u1) (fun zz => ((fun hh => hh u0) zz)))) h

theorem clause646 (x03 x13 x34 : ℝ) : ((¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th34 x03 x13 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 u1)))) h

theorem clause647 (t x12 x13 x23 : ℝ) : ((¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ ((t + ((-1) * x12) + x13) ≥ 1) ∨ (¬ (x13 ≥ 0)) ∨ ((t + ((-1) * x23)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x12) + x13) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th35 t x12 x13 x23
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u3 u0))))) h

theorem clause648 (t x23 : ℝ) : ((¬ ((t + ((-1) * x23)) ≤ 0)) ∨ (t ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x23) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th36 t x23
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause650 (t x23 : ℝ) : ((¬ (t ≤ x23)) ∨ (¬ (x23 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x23 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th37 t x23
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause652 (t x23 : ℝ) (h : (x23 < t)) : ((x23 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 < t) := fun hh => hn hh
  exact u0 h

theorem clause653 (x13 : ℝ) (h : (x13 ≥ 0)) : ((x13 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause654 (t x01 x03 x12 x13 x34 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
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
  have u5 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th40 t x01 x03 x12 x13 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u5 (And.intro u1 u3))))))) h

theorem clause656 (t x23 x24 x34 : ℝ) : (((x23 + ((-1) * x24)) ≤ 0) ∨ ((x24 + ((-1) * x34)) ≥ 0) ∨ (¬ (x23 ≤ x24)) ∨ (¬ (x24 ≤ x34)) ∨ (¬ ((x34 - x23) ≥ 1)) ∨ (¬ ((x24 - x23) ≤ (t - 1))) ∨ (¬ ((x34 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x34)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th43 t x23 x24 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause658 (t x23 x24 x34 : ℝ) : (((x23 + ((-1) * x24)) ≤ 0) ∨ ((x23 + ((-1) * x34)) ≥ 1) ∨ (¬ (x23 ≤ x24)) ∨ (¬ (x24 ≤ x34)) ∨ (¬ ((x34 - x23) ≥ 1)) ∨ (¬ ((x24 - x23) ≤ (t - 1))) ∨ (¬ ((x34 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th43 t x23 x24 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause662 (t x23 x24 x34 : ℝ) : (((x24 + ((-1) * x34)) ≤ 0) ∨ ((x23 + ((-1) * x24)) ≥ 0) ∨ (¬ (x23 ≤ x24)) ∨ (¬ (x24 ≤ x34)) ∨ (¬ ((x34 - x23) ≥ 1)) ∨ (¬ ((x24 - x23) ≤ (t - 1))) ∨ (¬ ((x34 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x24)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th43 t x23 x24 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause663 (t x23 x24 x34 : ℝ) : (((x24 + ((-1) * x34)) ≤ 0) ∨ ((x23 + ((-1) * x34)) ≥ 1) ∨ (¬ (x23 ≤ x24)) ∨ (¬ (x24 ≤ x34)) ∨ (¬ ((x34 - x23) ≥ 1)) ∨ (¬ ((x24 - x23) ≤ (t - 1))) ∨ (¬ ((x34 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th43 t x23 x24 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause665 (t x23 x24 x34 : ℝ) : (((x24 + ((-1) * x34)) ≤ 0) ∨ ((t + ((-1) * x24) + x34) ≥ 1) ∨ (¬ (x23 ≤ x24)) ∨ (¬ (x24 ≤ x34)) ∨ (¬ ((x34 - x23) ≥ 1)) ∨ (¬ ((x24 - x23) ≤ (t - 1))) ∨ (¬ ((x34 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x24) + x34) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th43 t x23 x24 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause666 (t x23 x24 x34 : ℝ) : (((x23 + ((-1) * x34)) ≤ (-1)) ∨ ((x24 + ((-1) * x34)) ≥ 0) ∨ (¬ (x23 ≤ x24)) ∨ (¬ (x24 ≤ x34)) ∨ (¬ ((x34 - x23) ≥ 1)) ∨ (¬ ((x24 - x23) ≤ (t - 1))) ∨ (¬ ((x34 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x34)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th43 t x23 x24 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause667 (t x23 x24 x34 : ℝ) : (((x23 + ((-1) * x34)) ≤ (-1)) ∨ ((x23 + ((-1) * x24)) ≥ 0) ∨ (¬ (x23 ≤ x24)) ∨ (¬ (x24 ≤ x34)) ∨ (¬ ((x34 - x23) ≥ 1)) ∨ (¬ ((x24 - x23) ≤ (t - 1))) ∨ (¬ ((x34 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x24)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th43 t x23 x24 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause668 (t x23 x24 x34 : ℝ) : (((x23 + ((-1) * x34)) ≤ (-1)) ∨ ((x23 + ((-1) * x34)) ≥ 1) ∨ (¬ (x23 ≤ x24)) ∨ (¬ (x24 ≤ x34)) ∨ (¬ ((x34 - x23) ≥ 1)) ∨ (¬ ((x24 - x23) ≤ (t - 1))) ∨ (¬ ((x34 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th43 t x23 x24 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause669 (t x23 x24 x34 : ℝ) : (((x23 + ((-1) * x34)) ≤ (-1)) ∨ ((t + ((-1) * x23) + x24) ≥ 1) ∨ (¬ (x23 ≤ x24)) ∨ (¬ (x24 ≤ x34)) ∨ (¬ ((x34 - x23) ≥ 1)) ∨ (¬ ((x24 - x23) ≤ (t - 1))) ∨ (¬ ((x34 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x23) + x24) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th43 t x23 x24 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause673 (t x23 x24 x34 : ℝ) : (((t + x23 + ((-1) * x24)) ≥ 1) ∨ ((x23 + ((-1) * x34)) ≥ 1) ∨ (¬ (x23 ≤ x24)) ∨ (¬ (x24 ≤ x34)) ∨ (¬ ((x34 - x23) ≥ 1)) ∨ (¬ ((x24 - x23) ≤ (t - 1))) ∨ (¬ ((x34 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x23 + ((-1) * x24)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th43 t x23 x24 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause676 (t x23 x24 x34 : ℝ) : (((t + x24 + ((-1) * x34)) ≥ 1) ∨ ((x24 + ((-1) * x34)) ≥ 0) ∨ (¬ (x23 ≤ x24)) ∨ (¬ (x24 ≤ x34)) ∨ (¬ ((x34 - x23) ≥ 1)) ∨ (¬ ((x24 - x23) ≤ (t - 1))) ∨ (¬ ((x34 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x24 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x34)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th43 t x23 x24 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause678 (t x23 x24 x34 : ℝ) : (((t + x24 + ((-1) * x34)) ≥ 1) ∨ ((x23 + ((-1) * x34)) ≥ 1) ∨ (¬ (x23 ≤ x24)) ∨ (¬ (x24 ≤ x34)) ∨ (¬ ((x34 - x23) ≥ 1)) ∨ (¬ ((x24 - x23) ≤ (t - 1))) ∨ (¬ ((x34 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x24 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th43 t x23 x24 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause681 (t x23 x24 x34 : ℝ) : (((x23 + ((-1) * x24)) ≤ 0) ∨ ((x24 + ((-1) * x34)) ≥ 0) ∨ (¬ (x34 ≤ x24)) ∨ (¬ (x24 ≤ x23)) ∨ (¬ ((x23 - x34) ≥ 1)) ∨ (¬ ((x23 - x24) ≤ (t - 1))) ∨ (¬ ((x24 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x34)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th43 t x23 x24 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause683 (t x23 x24 x34 : ℝ) : (((x23 + ((-1) * x24)) ≤ 0) ∨ ((x23 + ((-1) * x34)) ≥ 1) ∨ (¬ (x34 ≤ x24)) ∨ (¬ (x24 ≤ x23)) ∨ (¬ ((x23 - x34) ≥ 1)) ∨ (¬ ((x23 - x24) ≤ (t - 1))) ∨ (¬ ((x24 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th43 t x23 x24 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause684 (t x23 x24 x34 : ℝ) : (((t + ((-1) * x23) + x24) ≥ 1) ∨ ((x23 + ((-1) * x24)) ≤ 0) ∨ (¬ (x34 ≤ x24)) ∨ (¬ (x24 ≤ x23)) ∨ (¬ ((x23 - x34) ≥ 1)) ∨ (¬ ((x23 - x24) ≤ (t - 1))) ∨ (¬ ((x24 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x23) + x24) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th43 t x23 x24 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause687 (t x23 x24 x34 : ℝ) : (((x24 + ((-1) * x34)) ≤ 0) ∨ ((x23 + ((-1) * x24)) ≥ 0) ∨ (¬ (x34 ≤ x24)) ∨ (¬ (x24 ≤ x23)) ∨ (¬ ((x23 - x34) ≥ 1)) ∨ (¬ ((x23 - x24) ≤ (t - 1))) ∨ (¬ ((x24 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x24)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th43 t x23 x24 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause688 (t x23 x24 x34 : ℝ) : (((x24 + ((-1) * x34)) ≤ 0) ∨ ((x23 + ((-1) * x34)) ≥ 1) ∨ (¬ (x34 ≤ x24)) ∨ (¬ (x24 ≤ x23)) ∨ (¬ ((x23 - x34) ≥ 1)) ∨ (¬ ((x23 - x24) ≤ (t - 1))) ∨ (¬ ((x24 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th43 t x23 x24 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause691 (t x23 x24 x34 : ℝ) : (((x23 + ((-1) * x34)) ≤ (-1)) ∨ ((x24 + ((-1) * x34)) ≥ 0) ∨ (¬ (x34 ≤ x24)) ∨ (¬ (x24 ≤ x23)) ∨ (¬ ((x23 - x34) ≥ 1)) ∨ (¬ ((x23 - x24) ≤ (t - 1))) ∨ (¬ ((x24 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x34)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th43 t x23 x24 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause692 (t x23 x24 x34 : ℝ) : (((x23 + ((-1) * x34)) ≤ (-1)) ∨ ((x23 + ((-1) * x24)) ≥ 0) ∨ (¬ (x34 ≤ x24)) ∨ (¬ (x24 ≤ x23)) ∨ (¬ ((x23 - x34) ≥ 1)) ∨ (¬ ((x23 - x24) ≤ (t - 1))) ∨ (¬ ((x24 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x24)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th43 t x23 x24 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause693 (t x23 x24 x34 : ℝ) : (((x23 + ((-1) * x34)) ≤ (-1)) ∨ ((x23 + ((-1) * x34)) ≥ 1) ∨ (¬ (x34 ≤ x24)) ∨ (¬ (x24 ≤ x23)) ∨ (¬ ((x23 - x34) ≥ 1)) ∨ (¬ ((x23 - x24) ≤ (t - 1))) ∨ (¬ ((x24 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th43 t x23 x24 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause695 (t x23 x24 x34 : ℝ) : (((x23 + ((-1) * x34)) ≤ (-1)) ∨ ((t + ((-1) * x24) + x34) ≥ 1) ∨ (¬ (x34 ≤ x24)) ∨ (¬ (x24 ≤ x23)) ∨ (¬ ((x23 - x34) ≥ 1)) ∨ (¬ ((x23 - x24) ≤ (t - 1))) ∨ (¬ ((x24 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x24) + x34) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th43 t x23 x24 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause697 (t x23 x24 x34 : ℝ) : (((t + x23 + ((-1) * x24)) ≥ 1) ∨ ((x23 + ((-1) * x24)) ≥ 0) ∨ (¬ (x34 ≤ x24)) ∨ (¬ (x24 ≤ x23)) ∨ (¬ ((x23 - x34) ≥ 1)) ∨ (¬ ((x23 - x24) ≤ (t - 1))) ∨ (¬ ((x24 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x23 + ((-1) * x24)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x24)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th43 t x23 x24 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause698 (t x23 x24 x34 : ℝ) : (((t + x23 + ((-1) * x24)) ≥ 1) ∨ ((x23 + ((-1) * x34)) ≥ 1) ∨ (¬ (x34 ≤ x24)) ∨ (¬ (x24 ≤ x23)) ∨ (¬ ((x23 - x34) ≥ 1)) ∨ (¬ ((x23 - x24) ≤ (t - 1))) ∨ (¬ ((x24 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x23 + ((-1) * x24)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th43 t x23 x24 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause703 (t x23 x24 x34 : ℝ) : (((t + x24 + ((-1) * x34)) ≥ 1) ∨ ((x23 + ((-1) * x34)) ≥ 1) ∨ (¬ (x34 ≤ x24)) ∨ (¬ (x24 ≤ x23)) ∨ (¬ ((x23 - x34) ≥ 1)) ∨ (¬ ((x23 - x24) ≤ (t - 1))) ∨ (¬ ((x24 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x24 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th43 t x23 x24 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause756 (t x23 x24 x34 : ℝ) (h : (((x23 ≤ x24) ∧ (x24 ≤ x34) ∧ ((x34 - x23) ≥ 1) ∧ ((x24 - x23) ≤ (t - 1)) ∧ ((x34 - x24) ≤ (t - 1))) ∨ ((x34 ≤ x24) ∧ (x24 ≤ x23) ∧ ((x23 - x34) ≥ 1) ∧ ((x23 - x24) ≤ (t - 1)) ∧ ((x24 - x34) ≤ (t - 1))))) : ((x23 ≤ x24) ∨ (x34 ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≤ x24) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x34 ≤ x24) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause757 (t x23 x24 x34 : ℝ) (h : (((x23 ≤ x24) ∧ (x24 ≤ x34) ∧ ((x34 - x23) ≥ 1) ∧ ((x24 - x23) ≤ (t - 1)) ∧ ((x34 - x24) ≤ (t - 1))) ∨ ((x34 ≤ x24) ∧ (x24 ≤ x23) ∧ ((x23 - x34) ≥ 1) ∧ ((x23 - x24) ≤ (t - 1)) ∧ ((x24 - x34) ≤ (t - 1))))) : ((x23 ≤ x24) ∨ (x24 ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≤ x24) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x24 ≤ x23) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause758 (t x23 x24 x34 : ℝ) (h : (((x23 ≤ x24) ∧ (x24 ≤ x34) ∧ ((x34 - x23) ≥ 1) ∧ ((x24 - x23) ≤ (t - 1)) ∧ ((x34 - x24) ≤ (t - 1))) ∨ ((x34 ≤ x24) ∧ (x24 ≤ x23) ∧ ((x23 - x34) ≥ 1) ∧ ((x23 - x24) ≤ (t - 1)) ∧ ((x24 - x34) ≤ (t - 1))))) : ((x23 ≤ x24) ∨ ((x23 - x34) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≤ x24) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x34) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause759 (t x23 x24 x34 : ℝ) (h : (((x23 ≤ x24) ∧ (x24 ≤ x34) ∧ ((x34 - x23) ≥ 1) ∧ ((x24 - x23) ≤ (t - 1)) ∧ ((x34 - x24) ≤ (t - 1))) ∨ ((x34 ≤ x24) ∧ (x24 ≤ x23) ∧ ((x23 - x34) ≥ 1) ∧ ((x23 - x24) ≤ (t - 1)) ∧ ((x24 - x34) ≤ (t - 1))))) : ((x23 ≤ x24) ∨ ((x23 - x24) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≤ x24) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x24) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause760 (t x23 x24 x34 : ℝ) (h : (((x23 ≤ x24) ∧ (x24 ≤ x34) ∧ ((x34 - x23) ≥ 1) ∧ ((x24 - x23) ≤ (t - 1)) ∧ ((x34 - x24) ≤ (t - 1))) ∨ ((x34 ≤ x24) ∧ (x24 ≤ x23) ∧ ((x23 - x34) ≥ 1) ∧ ((x23 - x24) ≤ (t - 1)) ∧ ((x24 - x34) ≤ (t - 1))))) : ((x23 ≤ x24) ∨ ((x24 - x34) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≤ x24) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x34) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause761 (t x23 x24 x34 : ℝ) (h : (((x23 ≤ x24) ∧ (x24 ≤ x34) ∧ ((x34 - x23) ≥ 1) ∧ ((x24 - x23) ≤ (t - 1)) ∧ ((x34 - x24) ≤ (t - 1))) ∨ ((x34 ≤ x24) ∧ (x24 ≤ x23) ∧ ((x23 - x34) ≥ 1) ∧ ((x23 - x24) ≤ (t - 1)) ∧ ((x24 - x34) ≤ (t - 1))))) : ((x24 ≤ x34) ∨ (x34 ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≤ x34) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x34 ≤ x24) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause762 (t x23 x24 x34 : ℝ) (h : (((x23 ≤ x24) ∧ (x24 ≤ x34) ∧ ((x34 - x23) ≥ 1) ∧ ((x24 - x23) ≤ (t - 1)) ∧ ((x34 - x24) ≤ (t - 1))) ∨ ((x34 ≤ x24) ∧ (x24 ≤ x23) ∧ ((x23 - x34) ≥ 1) ∧ ((x23 - x24) ≤ (t - 1)) ∧ ((x24 - x34) ≤ (t - 1))))) : ((x24 ≤ x34) ∨ (x24 ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≤ x34) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x24 ≤ x23) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause763 (t x23 x24 x34 : ℝ) (h : (((x23 ≤ x24) ∧ (x24 ≤ x34) ∧ ((x34 - x23) ≥ 1) ∧ ((x24 - x23) ≤ (t - 1)) ∧ ((x34 - x24) ≤ (t - 1))) ∨ ((x34 ≤ x24) ∧ (x24 ≤ x23) ∧ ((x23 - x34) ≥ 1) ∧ ((x23 - x24) ≤ (t - 1)) ∧ ((x24 - x34) ≤ (t - 1))))) : ((x24 ≤ x34) ∨ ((x23 - x34) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≤ x34) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x34) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause764 (t x23 x24 x34 : ℝ) (h : (((x23 ≤ x24) ∧ (x24 ≤ x34) ∧ ((x34 - x23) ≥ 1) ∧ ((x24 - x23) ≤ (t - 1)) ∧ ((x34 - x24) ≤ (t - 1))) ∨ ((x34 ≤ x24) ∧ (x24 ≤ x23) ∧ ((x23 - x34) ≥ 1) ∧ ((x23 - x24) ≤ (t - 1)) ∧ ((x24 - x34) ≤ (t - 1))))) : ((x24 ≤ x34) ∨ ((x23 - x24) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≤ x34) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x24) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause765 (t x23 x24 x34 : ℝ) (h : (((x23 ≤ x24) ∧ (x24 ≤ x34) ∧ ((x34 - x23) ≥ 1) ∧ ((x24 - x23) ≤ (t - 1)) ∧ ((x34 - x24) ≤ (t - 1))) ∨ ((x34 ≤ x24) ∧ (x24 ≤ x23) ∧ ((x23 - x34) ≥ 1) ∧ ((x23 - x24) ≤ (t - 1)) ∧ ((x24 - x34) ≤ (t - 1))))) : ((x24 ≤ x34) ∨ ((x24 - x34) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≤ x34) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x34) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause766 (t x23 x24 x34 : ℝ) (h : (((x23 ≤ x24) ∧ (x24 ≤ x34) ∧ ((x34 - x23) ≥ 1) ∧ ((x24 - x23) ≤ (t - 1)) ∧ ((x34 - x24) ≤ (t - 1))) ∨ ((x34 ≤ x24) ∧ (x24 ≤ x23) ∧ ((x23 - x34) ≥ 1) ∧ ((x23 - x24) ≤ (t - 1)) ∧ ((x24 - x34) ≤ (t - 1))))) : (((x34 - x23) ≥ 1) ∨ (x34 ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x23) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x34 ≤ x24) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause767 (t x23 x24 x34 : ℝ) (h : (((x23 ≤ x24) ∧ (x24 ≤ x34) ∧ ((x34 - x23) ≥ 1) ∧ ((x24 - x23) ≤ (t - 1)) ∧ ((x34 - x24) ≤ (t - 1))) ∨ ((x34 ≤ x24) ∧ (x24 ≤ x23) ∧ ((x23 - x34) ≥ 1) ∧ ((x23 - x24) ≤ (t - 1)) ∧ ((x24 - x34) ≤ (t - 1))))) : (((x34 - x23) ≥ 1) ∨ (x24 ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x23) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x24 ≤ x23) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause768 (t x23 x24 x34 : ℝ) (h : (((x23 ≤ x24) ∧ (x24 ≤ x34) ∧ ((x34 - x23) ≥ 1) ∧ ((x24 - x23) ≤ (t - 1)) ∧ ((x34 - x24) ≤ (t - 1))) ∨ ((x34 ≤ x24) ∧ (x24 ≤ x23) ∧ ((x23 - x34) ≥ 1) ∧ ((x23 - x24) ≤ (t - 1)) ∧ ((x24 - x34) ≤ (t - 1))))) : (((x34 - x23) ≥ 1) ∨ ((x23 - x34) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x23) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x34) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause769 (t x23 x24 x34 : ℝ) (h : (((x23 ≤ x24) ∧ (x24 ≤ x34) ∧ ((x34 - x23) ≥ 1) ∧ ((x24 - x23) ≤ (t - 1)) ∧ ((x34 - x24) ≤ (t - 1))) ∨ ((x34 ≤ x24) ∧ (x24 ≤ x23) ∧ ((x23 - x34) ≥ 1) ∧ ((x23 - x24) ≤ (t - 1)) ∧ ((x24 - x34) ≤ (t - 1))))) : (((x34 - x23) ≥ 1) ∨ ((x23 - x24) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x23) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x24) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause770 (t x23 x24 x34 : ℝ) (h : (((x23 ≤ x24) ∧ (x24 ≤ x34) ∧ ((x34 - x23) ≥ 1) ∧ ((x24 - x23) ≤ (t - 1)) ∧ ((x34 - x24) ≤ (t - 1))) ∨ ((x34 ≤ x24) ∧ (x24 ≤ x23) ∧ ((x23 - x34) ≥ 1) ∧ ((x23 - x24) ≤ (t - 1)) ∧ ((x24 - x34) ≤ (t - 1))))) : (((x34 - x23) ≥ 1) ∨ ((x24 - x34) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x23) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x34) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause771 (t x23 x24 x34 : ℝ) (h : (((x23 ≤ x24) ∧ (x24 ≤ x34) ∧ ((x34 - x23) ≥ 1) ∧ ((x24 - x23) ≤ (t - 1)) ∧ ((x34 - x24) ≤ (t - 1))) ∨ ((x34 ≤ x24) ∧ (x24 ≤ x23) ∧ ((x23 - x34) ≥ 1) ∧ ((x23 - x24) ≤ (t - 1)) ∧ ((x24 - x34) ≤ (t - 1))))) : (((x24 - x23) ≤ (t - 1)) ∨ (x34 ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 - x23) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x34 ≤ x24) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause772 (t x23 x24 x34 : ℝ) (h : (((x23 ≤ x24) ∧ (x24 ≤ x34) ∧ ((x34 - x23) ≥ 1) ∧ ((x24 - x23) ≤ (t - 1)) ∧ ((x34 - x24) ≤ (t - 1))) ∨ ((x34 ≤ x24) ∧ (x24 ≤ x23) ∧ ((x23 - x34) ≥ 1) ∧ ((x23 - x24) ≤ (t - 1)) ∧ ((x24 - x34) ≤ (t - 1))))) : (((x24 - x23) ≤ (t - 1)) ∨ (x24 ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 - x23) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x24 ≤ x23) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause773 (t x23 x24 x34 : ℝ) (h : (((x23 ≤ x24) ∧ (x24 ≤ x34) ∧ ((x34 - x23) ≥ 1) ∧ ((x24 - x23) ≤ (t - 1)) ∧ ((x34 - x24) ≤ (t - 1))) ∨ ((x34 ≤ x24) ∧ (x24 ≤ x23) ∧ ((x23 - x34) ≥ 1) ∧ ((x23 - x24) ≤ (t - 1)) ∧ ((x24 - x34) ≤ (t - 1))))) : (((x24 - x23) ≤ (t - 1)) ∨ ((x23 - x34) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 - x23) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x34) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause774 (t x23 x24 x34 : ℝ) (h : (((x23 ≤ x24) ∧ (x24 ≤ x34) ∧ ((x34 - x23) ≥ 1) ∧ ((x24 - x23) ≤ (t - 1)) ∧ ((x34 - x24) ≤ (t - 1))) ∨ ((x34 ≤ x24) ∧ (x24 ≤ x23) ∧ ((x23 - x34) ≥ 1) ∧ ((x23 - x24) ≤ (t - 1)) ∧ ((x24 - x34) ≤ (t - 1))))) : (((x24 - x23) ≤ (t - 1)) ∨ ((x23 - x24) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 - x23) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x24) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause775 (t x23 x24 x34 : ℝ) (h : (((x23 ≤ x24) ∧ (x24 ≤ x34) ∧ ((x34 - x23) ≥ 1) ∧ ((x24 - x23) ≤ (t - 1)) ∧ ((x34 - x24) ≤ (t - 1))) ∨ ((x34 ≤ x24) ∧ (x24 ≤ x23) ∧ ((x23 - x34) ≥ 1) ∧ ((x23 - x24) ≤ (t - 1)) ∧ ((x24 - x34) ≤ (t - 1))))) : (((x24 - x23) ≤ (t - 1)) ∨ ((x24 - x34) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 - x23) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x34) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause776 (t x23 x24 x34 : ℝ) (h : (((x23 ≤ x24) ∧ (x24 ≤ x34) ∧ ((x34 - x23) ≥ 1) ∧ ((x24 - x23) ≤ (t - 1)) ∧ ((x34 - x24) ≤ (t - 1))) ∨ ((x34 ≤ x24) ∧ (x24 ≤ x23) ∧ ((x23 - x34) ≥ 1) ∧ ((x23 - x24) ≤ (t - 1)) ∧ ((x24 - x34) ≤ (t - 1))))) : (((x34 - x24) ≤ (t - 1)) ∨ (x34 ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x24) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x34 ≤ x24) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause777 (t x23 x24 x34 : ℝ) (h : (((x23 ≤ x24) ∧ (x24 ≤ x34) ∧ ((x34 - x23) ≥ 1) ∧ ((x24 - x23) ≤ (t - 1)) ∧ ((x34 - x24) ≤ (t - 1))) ∨ ((x34 ≤ x24) ∧ (x24 ≤ x23) ∧ ((x23 - x34) ≥ 1) ∧ ((x23 - x24) ≤ (t - 1)) ∧ ((x24 - x34) ≤ (t - 1))))) : (((x34 - x24) ≤ (t - 1)) ∨ (x24 ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x24) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x24 ≤ x23) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause778 (t x23 x24 x34 : ℝ) (h : (((x23 ≤ x24) ∧ (x24 ≤ x34) ∧ ((x34 - x23) ≥ 1) ∧ ((x24 - x23) ≤ (t - 1)) ∧ ((x34 - x24) ≤ (t - 1))) ∨ ((x34 ≤ x24) ∧ (x24 ≤ x23) ∧ ((x23 - x34) ≥ 1) ∧ ((x23 - x24) ≤ (t - 1)) ∧ ((x24 - x34) ≤ (t - 1))))) : (((x34 - x24) ≤ (t - 1)) ∨ ((x23 - x34) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x24) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x34) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause779 (t x23 x24 x34 : ℝ) (h : (((x23 ≤ x24) ∧ (x24 ≤ x34) ∧ ((x34 - x23) ≥ 1) ∧ ((x24 - x23) ≤ (t - 1)) ∧ ((x34 - x24) ≤ (t - 1))) ∨ ((x34 ≤ x24) ∧ (x24 ≤ x23) ∧ ((x23 - x34) ≥ 1) ∧ ((x23 - x24) ≤ (t - 1)) ∧ ((x24 - x34) ≤ (t - 1))))) : (((x34 - x24) ≤ (t - 1)) ∨ ((x23 - x24) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x24) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x24) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause780 (t x23 x24 x34 : ℝ) (h : (((x23 ≤ x24) ∧ (x24 ≤ x34) ∧ ((x34 - x23) ≥ 1) ∧ ((x24 - x23) ≤ (t - 1)) ∧ ((x34 - x24) ≤ (t - 1))) ∨ ((x34 ≤ x24) ∧ (x24 ≤ x23) ∧ ((x23 - x34) ≥ 1) ∧ ((x23 - x24) ≤ (t - 1)) ∧ ((x24 - x34) ≤ (t - 1))))) : (((x34 - x24) ≤ (t - 1)) ∨ ((x24 - x34) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x24) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x34) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause781 (t x03 : ℝ) : ((¬ ((t + ((-1) * x03)) ≤ 0)) ∨ (t ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x03) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th45 t x03
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause783 (t x03 : ℝ) : ((¬ (t ≤ x03)) ∨ (¬ (x03 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x03 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th46 t x03
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause785 (t x03 : ℝ) (h : (x03 < t)) : ((x03 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 < t) := fun hh => hn hh
  exact u0 h

theorem clause786 (x24 : ℝ) (h : (x24 ≥ 0)) : ((x24 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause787 (t x05 x07 x12 x17 x23 x25 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((t + x23 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x07)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x17)) ≤ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x23 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x05 + ((-1) * x07)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x17)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th49 t x05 x07 x12 x17 x23 x25 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u4 (And.intro u5 (And.intro u6 u7))))))))) h

theorem clause788 (t x23 x25 x35 : ℝ) : (((t + x23 + ((-1) * x25)) ≥ 1) ∨ ((t + ((-1) * x25)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ (x35 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x23 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x25)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th50 t x23 x25 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u2 u3))))) h

theorem clause789 (x35 : ℝ) (h : (x35 ≥ 0)) : ((x35 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x35 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause790 (t x23 x25 x35 : ℝ) : (((x23 + ((-1) * x25)) ≤ 0) ∨ ((x25 + ((-1) * x35)) ≥ 0) ∨ (¬ (x23 ≤ x25)) ∨ (¬ (x25 ≤ x35)) ∨ (¬ ((x35 - x23) ≥ 1)) ∨ (¬ ((x25 - x23) ≤ (t - 1))) ∨ (¬ ((x35 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x25)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x35)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th53 t x23 x25 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause792 (t x23 x25 x35 : ℝ) : (((x23 + ((-1) * x35)) ≥ 1) ∨ ((x23 + ((-1) * x25)) ≤ 0) ∨ (¬ (x23 ≤ x25)) ∨ (¬ (x25 ≤ x35)) ∨ (¬ ((x35 - x23) ≥ 1)) ∨ (¬ ((x25 - x23) ≤ (t - 1))) ∨ (¬ ((x35 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x25)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th53 t x23 x25 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause793 (t x23 x25 x35 : ℝ) : (((x23 + ((-1) * x25)) ≤ 0) ∨ ((t + ((-1) * x23) + x25) ≥ 1) ∨ (¬ (x23 ≤ x25)) ∨ (¬ (x25 ≤ x35)) ∨ (¬ ((x35 - x23) ≥ 1)) ∨ (¬ ((x25 - x23) ≤ (t - 1))) ∨ (¬ ((x35 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x25)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x23) + x25) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th53 t x23 x25 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause796 (t x23 x25 x35 : ℝ) : (((x25 + ((-1) * x35)) ≤ 0) ∨ ((x23 + ((-1) * x25)) ≥ 0) ∨ (¬ (x23 ≤ x25)) ∨ (¬ (x25 ≤ x35)) ∨ (¬ ((x35 - x23) ≥ 1)) ∨ (¬ ((x25 - x23) ≤ (t - 1))) ∨ (¬ ((x35 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x25)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th53 t x23 x25 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause797 (t x23 x25 x35 : ℝ) : (((x23 + ((-1) * x35)) ≥ 1) ∨ ((x25 + ((-1) * x35)) ≤ 0) ∨ (¬ (x23 ≤ x25)) ∨ (¬ (x25 ≤ x35)) ∨ (¬ ((x35 - x23) ≥ 1)) ∨ (¬ ((x25 - x23) ≤ (t - 1))) ∨ (¬ ((x35 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th53 t x23 x25 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause799 (t x23 x25 x35 : ℝ) : (((x25 + ((-1) * x35)) ≤ 0) ∨ ((t + ((-1) * x25) + x35) ≥ 1) ∨ (¬ (x23 ≤ x25)) ∨ (¬ (x25 ≤ x35)) ∨ (¬ ((x35 - x23) ≥ 1)) ∨ (¬ ((x25 - x23) ≤ (t - 1))) ∨ (¬ ((x35 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x25) + x35) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th53 t x23 x25 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause800 (t x23 x25 x35 : ℝ) : (((x23 + ((-1) * x35)) ≤ (-1)) ∨ ((x25 + ((-1) * x35)) ≥ 0) ∨ (¬ (x23 ≤ x25)) ∨ (¬ (x25 ≤ x35)) ∨ (¬ ((x35 - x23) ≥ 1)) ∨ (¬ ((x25 - x23) ≤ (t - 1))) ∨ (¬ ((x35 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x35)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th53 t x23 x25 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause801 (t x23 x25 x35 : ℝ) : (((x23 + ((-1) * x35)) ≤ (-1)) ∨ ((x23 + ((-1) * x25)) ≥ 0) ∨ (¬ (x23 ≤ x25)) ∨ (¬ (x25 ≤ x35)) ∨ (¬ ((x35 - x23) ≥ 1)) ∨ (¬ ((x25 - x23) ≤ (t - 1))) ∨ (¬ ((x35 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x25)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th53 t x23 x25 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause802 (t x23 x25 x35 : ℝ) : (((x23 + ((-1) * x35)) ≥ 1) ∨ ((x23 + ((-1) * x35)) ≤ (-1)) ∨ (¬ (x23 ≤ x25)) ∨ (¬ (x25 ≤ x35)) ∨ (¬ ((x35 - x23) ≥ 1)) ∨ (¬ ((x25 - x23) ≤ (t - 1))) ∨ (¬ ((x35 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th53 t x23 x25 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause803 (t x23 x25 x35 : ℝ) : (((x23 + ((-1) * x35)) ≤ (-1)) ∨ ((t + ((-1) * x23) + x25) ≥ 1) ∨ (¬ (x23 ≤ x25)) ∨ (¬ (x25 ≤ x35)) ∨ (¬ ((x35 - x23) ≥ 1)) ∨ (¬ ((x25 - x23) ≤ (t - 1))) ∨ (¬ ((x35 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x23) + x25) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th53 t x23 x25 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause804 (t x23 x25 x35 : ℝ) : (((x23 + ((-1) * x35)) ≤ (-1)) ∨ ((t + ((-1) * x25) + x35) ≥ 1) ∨ (¬ (x23 ≤ x25)) ∨ (¬ (x25 ≤ x35)) ∨ (¬ ((x35 - x23) ≥ 1)) ∨ (¬ ((x25 - x23) ≤ (t - 1))) ∨ (¬ ((x35 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x25) + x35) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th53 t x23 x25 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause807 (t x23 x25 x35 : ℝ) : (((t + x23 + ((-1) * x25)) ≥ 1) ∨ ((x23 + ((-1) * x35)) ≥ 1) ∨ (¬ (x23 ≤ x25)) ∨ (¬ (x25 ≤ x35)) ∨ (¬ ((x35 - x23) ≥ 1)) ∨ (¬ ((x25 - x23) ≤ (t - 1))) ∨ (¬ ((x35 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x23 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th53 t x23 x25 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause810 (t x23 x25 x35 : ℝ) : (((t + x25 + ((-1) * x35)) ≥ 1) ∨ ((x25 + ((-1) * x35)) ≥ 0) ∨ (¬ (x23 ≤ x25)) ∨ (¬ (x25 ≤ x35)) ∨ (¬ ((x35 - x23) ≥ 1)) ∨ (¬ ((x25 - x23) ≤ (t - 1))) ∨ (¬ ((x35 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x25 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x35)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th53 t x23 x25 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause812 (t x23 x25 x35 : ℝ) : (((x23 + ((-1) * x35)) ≥ 1) ∨ ((t + x25 + ((-1) * x35)) ≥ 1) ∨ (¬ (x23 ≤ x25)) ∨ (¬ (x25 ≤ x35)) ∨ (¬ ((x35 - x23) ≥ 1)) ∨ (¬ ((x25 - x23) ≤ (t - 1))) ∨ (¬ ((x35 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x25 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th53 t x23 x25 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause817 (t x23 x25 x35 : ℝ) : (((x23 + ((-1) * x35)) ≥ 1) ∨ ((x23 + ((-1) * x25)) ≤ 0) ∨ (¬ (x35 ≤ x25)) ∨ (¬ (x25 ≤ x23)) ∨ (¬ ((x23 - x35) ≥ 1)) ∨ (¬ ((x23 - x25) ≤ (t - 1))) ∨ (¬ ((x25 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x25)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th53 t x23 x25 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause818 (t x23 x25 x35 : ℝ) : (((x23 + ((-1) * x25)) ≤ 0) ∨ ((t + ((-1) * x23) + x25) ≥ 1) ∨ (¬ (x35 ≤ x25)) ∨ (¬ (x25 ≤ x23)) ∨ (¬ ((x23 - x35) ≥ 1)) ∨ (¬ ((x23 - x25) ≤ (t - 1))) ∨ (¬ ((x25 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x25)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x23) + x25) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th53 t x23 x25 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause822 (t x23 x25 x35 : ℝ) : (((x23 + ((-1) * x35)) ≥ 1) ∨ ((x25 + ((-1) * x35)) ≤ 0) ∨ (¬ (x35 ≤ x25)) ∨ (¬ (x25 ≤ x23)) ∨ (¬ ((x23 - x35) ≥ 1)) ∨ (¬ ((x23 - x25) ≤ (t - 1))) ∨ (¬ ((x25 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th53 t x23 x25 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause824 (t x23 x25 x35 : ℝ) : (((x25 + ((-1) * x35)) ≤ 0) ∨ ((t + ((-1) * x25) + x35) ≥ 1) ∨ (¬ (x35 ≤ x25)) ∨ (¬ (x25 ≤ x23)) ∨ (¬ ((x23 - x35) ≥ 1)) ∨ (¬ ((x23 - x25) ≤ (t - 1))) ∨ (¬ ((x25 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x25) + x35) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th53 t x23 x25 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause825 (t x23 x25 x35 : ℝ) : (((x23 + ((-1) * x35)) ≤ (-1)) ∨ ((x25 + ((-1) * x35)) ≥ 0) ∨ (¬ (x35 ≤ x25)) ∨ (¬ (x25 ≤ x23)) ∨ (¬ ((x23 - x35) ≥ 1)) ∨ (¬ ((x23 - x25) ≤ (t - 1))) ∨ (¬ ((x25 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x35)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th53 t x23 x25 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause826 (t x23 x25 x35 : ℝ) : (((x23 + ((-1) * x35)) ≤ (-1)) ∨ ((x23 + ((-1) * x25)) ≥ 0) ∨ (¬ (x35 ≤ x25)) ∨ (¬ (x25 ≤ x23)) ∨ (¬ ((x23 - x35) ≥ 1)) ∨ (¬ ((x23 - x25) ≤ (t - 1))) ∨ (¬ ((x25 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x25)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th53 t x23 x25 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause827 (t x23 x25 x35 : ℝ) : (((x23 + ((-1) * x35)) ≥ 1) ∨ ((x23 + ((-1) * x35)) ≤ (-1)) ∨ (¬ (x35 ≤ x25)) ∨ (¬ (x25 ≤ x23)) ∨ (¬ ((x23 - x35) ≥ 1)) ∨ (¬ ((x23 - x25) ≤ (t - 1))) ∨ (¬ ((x25 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th53 t x23 x25 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause831 (t x23 x25 x35 : ℝ) : (((t + x23 + ((-1) * x25)) ≥ 1) ∨ ((x23 + ((-1) * x25)) ≥ 0) ∨ (¬ (x35 ≤ x25)) ∨ (¬ (x25 ≤ x23)) ∨ (¬ ((x23 - x35) ≥ 1)) ∨ (¬ ((x23 - x25) ≤ (t - 1))) ∨ (¬ ((x25 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x23 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x25)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th53 t x23 x25 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause832 (t x23 x25 x35 : ℝ) : (((t + x23 + ((-1) * x25)) ≥ 1) ∨ ((x23 + ((-1) * x35)) ≥ 1) ∨ (¬ (x35 ≤ x25)) ∨ (¬ (x25 ≤ x23)) ∨ (¬ ((x23 - x35) ≥ 1)) ∨ (¬ ((x23 - x25) ≤ (t - 1))) ∨ (¬ ((x25 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x23 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th53 t x23 x25 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause835 (t x23 x25 x35 : ℝ) : (((t + x25 + ((-1) * x35)) ≥ 1) ∨ ((x25 + ((-1) * x35)) ≥ 0) ∨ (¬ (x35 ≤ x25)) ∨ (¬ (x25 ≤ x23)) ∨ (¬ ((x23 - x35) ≥ 1)) ∨ (¬ ((x23 - x25) ≤ (t - 1))) ∨ (¬ ((x25 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x25 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x35)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th53 t x23 x25 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause890 (t x23 x25 x35 : ℝ) (h : (((x23 ≤ x25) ∧ (x25 ≤ x35) ∧ ((x35 - x23) ≥ 1) ∧ ((x25 - x23) ≤ (t - 1)) ∧ ((x35 - x25) ≤ (t - 1))) ∨ ((x35 ≤ x25) ∧ (x25 ≤ x23) ∧ ((x23 - x35) ≥ 1) ∧ ((x23 - x25) ≤ (t - 1)) ∧ ((x25 - x35) ≤ (t - 1))))) : ((x23 ≤ x25) ∨ (x35 ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≤ x25) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x35 ≤ x25) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause891 (t x23 x25 x35 : ℝ) (h : (((x23 ≤ x25) ∧ (x25 ≤ x35) ∧ ((x35 - x23) ≥ 1) ∧ ((x25 - x23) ≤ (t - 1)) ∧ ((x35 - x25) ≤ (t - 1))) ∨ ((x35 ≤ x25) ∧ (x25 ≤ x23) ∧ ((x23 - x35) ≥ 1) ∧ ((x23 - x25) ≤ (t - 1)) ∧ ((x25 - x35) ≤ (t - 1))))) : ((x23 ≤ x25) ∨ (x25 ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≤ x25) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x25 ≤ x23) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause892 (t x23 x25 x35 : ℝ) (h : (((x23 ≤ x25) ∧ (x25 ≤ x35) ∧ ((x35 - x23) ≥ 1) ∧ ((x25 - x23) ≤ (t - 1)) ∧ ((x35 - x25) ≤ (t - 1))) ∨ ((x35 ≤ x25) ∧ (x25 ≤ x23) ∧ ((x23 - x35) ≥ 1) ∧ ((x23 - x25) ≤ (t - 1)) ∧ ((x25 - x35) ≤ (t - 1))))) : ((x23 ≤ x25) ∨ ((x23 - x35) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≤ x25) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x35) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause893 (t x23 x25 x35 : ℝ) (h : (((x23 ≤ x25) ∧ (x25 ≤ x35) ∧ ((x35 - x23) ≥ 1) ∧ ((x25 - x23) ≤ (t - 1)) ∧ ((x35 - x25) ≤ (t - 1))) ∨ ((x35 ≤ x25) ∧ (x25 ≤ x23) ∧ ((x23 - x35) ≥ 1) ∧ ((x23 - x25) ≤ (t - 1)) ∧ ((x25 - x35) ≤ (t - 1))))) : ((x23 ≤ x25) ∨ ((x23 - x25) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≤ x25) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x25) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause894 (t x23 x25 x35 : ℝ) (h : (((x23 ≤ x25) ∧ (x25 ≤ x35) ∧ ((x35 - x23) ≥ 1) ∧ ((x25 - x23) ≤ (t - 1)) ∧ ((x35 - x25) ≤ (t - 1))) ∨ ((x35 ≤ x25) ∧ (x25 ≤ x23) ∧ ((x23 - x35) ≥ 1) ∧ ((x23 - x25) ≤ (t - 1)) ∧ ((x25 - x35) ≤ (t - 1))))) : ((x23 ≤ x25) ∨ ((x25 - x35) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≤ x25) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x35) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause895 (t x23 x25 x35 : ℝ) (h : (((x23 ≤ x25) ∧ (x25 ≤ x35) ∧ ((x35 - x23) ≥ 1) ∧ ((x25 - x23) ≤ (t - 1)) ∧ ((x35 - x25) ≤ (t - 1))) ∨ ((x35 ≤ x25) ∧ (x25 ≤ x23) ∧ ((x23 - x35) ≥ 1) ∧ ((x23 - x25) ≤ (t - 1)) ∧ ((x25 - x35) ≤ (t - 1))))) : ((x25 ≤ x35) ∨ (x35 ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≤ x35) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x35 ≤ x25) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause896 (t x23 x25 x35 : ℝ) (h : (((x23 ≤ x25) ∧ (x25 ≤ x35) ∧ ((x35 - x23) ≥ 1) ∧ ((x25 - x23) ≤ (t - 1)) ∧ ((x35 - x25) ≤ (t - 1))) ∨ ((x35 ≤ x25) ∧ (x25 ≤ x23) ∧ ((x23 - x35) ≥ 1) ∧ ((x23 - x25) ≤ (t - 1)) ∧ ((x25 - x35) ≤ (t - 1))))) : ((x25 ≤ x35) ∨ (x25 ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≤ x35) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x25 ≤ x23) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause897 (t x23 x25 x35 : ℝ) (h : (((x23 ≤ x25) ∧ (x25 ≤ x35) ∧ ((x35 - x23) ≥ 1) ∧ ((x25 - x23) ≤ (t - 1)) ∧ ((x35 - x25) ≤ (t - 1))) ∨ ((x35 ≤ x25) ∧ (x25 ≤ x23) ∧ ((x23 - x35) ≥ 1) ∧ ((x23 - x25) ≤ (t - 1)) ∧ ((x25 - x35) ≤ (t - 1))))) : ((x25 ≤ x35) ∨ ((x23 - x35) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≤ x35) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x35) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause898 (t x23 x25 x35 : ℝ) (h : (((x23 ≤ x25) ∧ (x25 ≤ x35) ∧ ((x35 - x23) ≥ 1) ∧ ((x25 - x23) ≤ (t - 1)) ∧ ((x35 - x25) ≤ (t - 1))) ∨ ((x35 ≤ x25) ∧ (x25 ≤ x23) ∧ ((x23 - x35) ≥ 1) ∧ ((x23 - x25) ≤ (t - 1)) ∧ ((x25 - x35) ≤ (t - 1))))) : ((x25 ≤ x35) ∨ ((x23 - x25) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≤ x35) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x25) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause899 (t x23 x25 x35 : ℝ) (h : (((x23 ≤ x25) ∧ (x25 ≤ x35) ∧ ((x35 - x23) ≥ 1) ∧ ((x25 - x23) ≤ (t - 1)) ∧ ((x35 - x25) ≤ (t - 1))) ∨ ((x35 ≤ x25) ∧ (x25 ≤ x23) ∧ ((x23 - x35) ≥ 1) ∧ ((x23 - x25) ≤ (t - 1)) ∧ ((x25 - x35) ≤ (t - 1))))) : ((x25 ≤ x35) ∨ ((x25 - x35) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≤ x35) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x35) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause900 (t x23 x25 x35 : ℝ) (h : (((x23 ≤ x25) ∧ (x25 ≤ x35) ∧ ((x35 - x23) ≥ 1) ∧ ((x25 - x23) ≤ (t - 1)) ∧ ((x35 - x25) ≤ (t - 1))) ∨ ((x35 ≤ x25) ∧ (x25 ≤ x23) ∧ ((x23 - x35) ≥ 1) ∧ ((x23 - x25) ≤ (t - 1)) ∧ ((x25 - x35) ≤ (t - 1))))) : (((x35 - x23) ≥ 1) ∨ (x35 ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x23) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x35 ≤ x25) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause901 (t x23 x25 x35 : ℝ) (h : (((x23 ≤ x25) ∧ (x25 ≤ x35) ∧ ((x35 - x23) ≥ 1) ∧ ((x25 - x23) ≤ (t - 1)) ∧ ((x35 - x25) ≤ (t - 1))) ∨ ((x35 ≤ x25) ∧ (x25 ≤ x23) ∧ ((x23 - x35) ≥ 1) ∧ ((x23 - x25) ≤ (t - 1)) ∧ ((x25 - x35) ≤ (t - 1))))) : (((x35 - x23) ≥ 1) ∨ (x25 ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x23) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x25 ≤ x23) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause902 (t x23 x25 x35 : ℝ) (h : (((x23 ≤ x25) ∧ (x25 ≤ x35) ∧ ((x35 - x23) ≥ 1) ∧ ((x25 - x23) ≤ (t - 1)) ∧ ((x35 - x25) ≤ (t - 1))) ∨ ((x35 ≤ x25) ∧ (x25 ≤ x23) ∧ ((x23 - x35) ≥ 1) ∧ ((x23 - x25) ≤ (t - 1)) ∧ ((x25 - x35) ≤ (t - 1))))) : (((x35 - x23) ≥ 1) ∨ ((x23 - x35) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x23) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x35) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause903 (t x23 x25 x35 : ℝ) (h : (((x23 ≤ x25) ∧ (x25 ≤ x35) ∧ ((x35 - x23) ≥ 1) ∧ ((x25 - x23) ≤ (t - 1)) ∧ ((x35 - x25) ≤ (t - 1))) ∨ ((x35 ≤ x25) ∧ (x25 ≤ x23) ∧ ((x23 - x35) ≥ 1) ∧ ((x23 - x25) ≤ (t - 1)) ∧ ((x25 - x35) ≤ (t - 1))))) : (((x35 - x23) ≥ 1) ∨ ((x23 - x25) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x23) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x25) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause904 (t x23 x25 x35 : ℝ) (h : (((x23 ≤ x25) ∧ (x25 ≤ x35) ∧ ((x35 - x23) ≥ 1) ∧ ((x25 - x23) ≤ (t - 1)) ∧ ((x35 - x25) ≤ (t - 1))) ∨ ((x35 ≤ x25) ∧ (x25 ≤ x23) ∧ ((x23 - x35) ≥ 1) ∧ ((x23 - x25) ≤ (t - 1)) ∧ ((x25 - x35) ≤ (t - 1))))) : (((x35 - x23) ≥ 1) ∨ ((x25 - x35) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x23) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x35) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause905 (t x23 x25 x35 : ℝ) (h : (((x23 ≤ x25) ∧ (x25 ≤ x35) ∧ ((x35 - x23) ≥ 1) ∧ ((x25 - x23) ≤ (t - 1)) ∧ ((x35 - x25) ≤ (t - 1))) ∨ ((x35 ≤ x25) ∧ (x25 ≤ x23) ∧ ((x23 - x35) ≥ 1) ∧ ((x23 - x25) ≤ (t - 1)) ∧ ((x25 - x35) ≤ (t - 1))))) : (((x25 - x23) ≤ (t - 1)) ∨ (x35 ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x23) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x35 ≤ x25) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause906 (t x23 x25 x35 : ℝ) (h : (((x23 ≤ x25) ∧ (x25 ≤ x35) ∧ ((x35 - x23) ≥ 1) ∧ ((x25 - x23) ≤ (t - 1)) ∧ ((x35 - x25) ≤ (t - 1))) ∨ ((x35 ≤ x25) ∧ (x25 ≤ x23) ∧ ((x23 - x35) ≥ 1) ∧ ((x23 - x25) ≤ (t - 1)) ∧ ((x25 - x35) ≤ (t - 1))))) : (((x25 - x23) ≤ (t - 1)) ∨ (x25 ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x23) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x25 ≤ x23) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause907 (t x23 x25 x35 : ℝ) (h : (((x23 ≤ x25) ∧ (x25 ≤ x35) ∧ ((x35 - x23) ≥ 1) ∧ ((x25 - x23) ≤ (t - 1)) ∧ ((x35 - x25) ≤ (t - 1))) ∨ ((x35 ≤ x25) ∧ (x25 ≤ x23) ∧ ((x23 - x35) ≥ 1) ∧ ((x23 - x25) ≤ (t - 1)) ∧ ((x25 - x35) ≤ (t - 1))))) : (((x25 - x23) ≤ (t - 1)) ∨ ((x23 - x35) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x23) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x35) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause908 (t x23 x25 x35 : ℝ) (h : (((x23 ≤ x25) ∧ (x25 ≤ x35) ∧ ((x35 - x23) ≥ 1) ∧ ((x25 - x23) ≤ (t - 1)) ∧ ((x35 - x25) ≤ (t - 1))) ∨ ((x35 ≤ x25) ∧ (x25 ≤ x23) ∧ ((x23 - x35) ≥ 1) ∧ ((x23 - x25) ≤ (t - 1)) ∧ ((x25 - x35) ≤ (t - 1))))) : (((x25 - x23) ≤ (t - 1)) ∨ ((x23 - x25) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x23) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x25) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause909 (t x23 x25 x35 : ℝ) (h : (((x23 ≤ x25) ∧ (x25 ≤ x35) ∧ ((x35 - x23) ≥ 1) ∧ ((x25 - x23) ≤ (t - 1)) ∧ ((x35 - x25) ≤ (t - 1))) ∨ ((x35 ≤ x25) ∧ (x25 ≤ x23) ∧ ((x23 - x35) ≥ 1) ∧ ((x23 - x25) ≤ (t - 1)) ∧ ((x25 - x35) ≤ (t - 1))))) : (((x25 - x23) ≤ (t - 1)) ∨ ((x25 - x35) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x23) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x35) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause910 (t x23 x25 x35 : ℝ) (h : (((x23 ≤ x25) ∧ (x25 ≤ x35) ∧ ((x35 - x23) ≥ 1) ∧ ((x25 - x23) ≤ (t - 1)) ∧ ((x35 - x25) ≤ (t - 1))) ∨ ((x35 ≤ x25) ∧ (x25 ≤ x23) ∧ ((x23 - x35) ≥ 1) ∧ ((x23 - x25) ≤ (t - 1)) ∧ ((x25 - x35) ≤ (t - 1))))) : (((x35 - x25) ≤ (t - 1)) ∨ (x35 ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x25) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x35 ≤ x25) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause911 (t x23 x25 x35 : ℝ) (h : (((x23 ≤ x25) ∧ (x25 ≤ x35) ∧ ((x35 - x23) ≥ 1) ∧ ((x25 - x23) ≤ (t - 1)) ∧ ((x35 - x25) ≤ (t - 1))) ∨ ((x35 ≤ x25) ∧ (x25 ≤ x23) ∧ ((x23 - x35) ≥ 1) ∧ ((x23 - x25) ≤ (t - 1)) ∧ ((x25 - x35) ≤ (t - 1))))) : (((x35 - x25) ≤ (t - 1)) ∨ (x25 ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x25) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x25 ≤ x23) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause912 (t x23 x25 x35 : ℝ) (h : (((x23 ≤ x25) ∧ (x25 ≤ x35) ∧ ((x35 - x23) ≥ 1) ∧ ((x25 - x23) ≤ (t - 1)) ∧ ((x35 - x25) ≤ (t - 1))) ∨ ((x35 ≤ x25) ∧ (x25 ≤ x23) ∧ ((x23 - x35) ≥ 1) ∧ ((x23 - x25) ≤ (t - 1)) ∧ ((x25 - x35) ≤ (t - 1))))) : (((x35 - x25) ≤ (t - 1)) ∨ ((x23 - x35) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x25) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x35) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause913 (t x23 x25 x35 : ℝ) (h : (((x23 ≤ x25) ∧ (x25 ≤ x35) ∧ ((x35 - x23) ≥ 1) ∧ ((x25 - x23) ≤ (t - 1)) ∧ ((x35 - x25) ≤ (t - 1))) ∨ ((x35 ≤ x25) ∧ (x25 ≤ x23) ∧ ((x23 - x35) ≥ 1) ∧ ((x23 - x25) ≤ (t - 1)) ∧ ((x25 - x35) ≤ (t - 1))))) : (((x35 - x25) ≤ (t - 1)) ∨ ((x23 - x25) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x25) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x25) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause914 (t x23 x25 x35 : ℝ) (h : (((x23 ≤ x25) ∧ (x25 ≤ x35) ∧ ((x35 - x23) ≥ 1) ∧ ((x25 - x23) ≤ (t - 1)) ∧ ((x35 - x25) ≤ (t - 1))) ∨ ((x35 ≤ x25) ∧ (x25 ≤ x23) ∧ ((x23 - x35) ≥ 1) ∧ ((x23 - x25) ≤ (t - 1)) ∧ ((x25 - x35) ≤ (t - 1))))) : (((x35 - x25) ≤ (t - 1)) ∨ ((x25 - x35) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x25) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x35) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause915 (t x25 : ℝ) : ((¬ ((t + ((-1) * x25)) ≤ 0)) ∨ (t ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x25) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th55 t x25
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause917 (t x25 : ℝ) : ((¬ (t ≤ x25)) ∨ (¬ (x25 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x25 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th56 t x25
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause919 (t x25 : ℝ) (h : (x25 < t)) : ((x25 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 < t) := fun hh => hn hh
  exact u0 h

theorem clause920 (t x02 x03 x23 x25 x34 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((t + x23 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x23 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th58 t x02 x03 x23 x25 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u1 (And.intro u5 (And.intro u3 u2))))))) h

theorem clause921 (x03 x23 x34 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x23)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th59 x03 x23 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 u0)))) h

theorem clause922 (t x02 x03 x23 : ℝ) : (((x02 + ((-1) * x03)) ≤ 0) ∨ ((x03 + ((-1) * x23)) ≥ 0) ∨ (¬ (x02 ≤ x03)) ∨ (¬ (x03 ≤ x23)) ∨ (¬ ((x23 - x02) ≥ 1)) ∨ (¬ ((x03 - x02) ≤ (t - 1))) ∨ (¬ ((x23 - x03) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x03)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x23)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th61 t x02 x03 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause924 (t x02 x03 x23 : ℝ) : (((x02 + ((-1) * x03)) ≤ 0) ∨ ((x02 + ((-1) * x23)) ≥ 1) ∨ (¬ (x02 ≤ x03)) ∨ (¬ (x03 ≤ x23)) ∨ (¬ ((x23 - x02) ≥ 1)) ∨ (¬ ((x03 - x02) ≤ (t - 1))) ∨ (¬ ((x23 - x03) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x03)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th61 t x02 x03 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause925 (t x02 x03 x23 : ℝ) : (((x02 + ((-1) * x03)) ≤ 0) ∨ ((t + ((-1) * x02) + x03) ≥ 1) ∨ (¬ (x02 ≤ x03)) ∨ (¬ (x03 ≤ x23)) ∨ (¬ ((x23 - x02) ≥ 1)) ∨ (¬ ((x03 - x02) ≤ (t - 1))) ∨ (¬ ((x23 - x03) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x03)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x02) + x03) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th61 t x02 x03 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause928 (t x02 x03 x23 : ℝ) : (((x02 + ((-1) * x03)) ≥ 0) ∨ ((x03 + ((-1) * x23)) ≤ 0) ∨ (¬ (x02 ≤ x03)) ∨ (¬ (x03 ≤ x23)) ∨ (¬ ((x23 - x02) ≥ 1)) ∨ (¬ ((x03 - x02) ≤ (t - 1))) ∨ (¬ ((x23 - x03) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x03)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th61 t x02 x03 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause929 (t x02 x03 x23 : ℝ) : (((x03 + ((-1) * x23)) ≤ 0) ∨ ((x02 + ((-1) * x23)) ≥ 1) ∨ (¬ (x02 ≤ x03)) ∨ (¬ (x03 ≤ x23)) ∨ (¬ ((x23 - x02) ≥ 1)) ∨ (¬ ((x03 - x02) ≤ (t - 1))) ∨ (¬ ((x23 - x03) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th61 t x02 x03 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause930 (t x02 x03 x23 : ℝ) : (((x03 + ((-1) * x23)) ≤ 0) ∨ ((t + ((-1) * x02) + x03) ≥ 1) ∨ (¬ (x02 ≤ x03)) ∨ (¬ (x03 ≤ x23)) ∨ (¬ ((x23 - x02) ≥ 1)) ∨ (¬ ((x03 - x02) ≤ (t - 1))) ∨ (¬ ((x23 - x03) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x02) + x03) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th61 t x02 x03 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause931 (t x02 x03 x23 : ℝ) : (((x03 + ((-1) * x23)) ≤ 0) ∨ ((t + ((-1) * x03) + x23) ≥ 1) ∨ (¬ (x02 ≤ x03)) ∨ (¬ (x03 ≤ x23)) ∨ (¬ ((x23 - x02) ≥ 1)) ∨ (¬ ((x03 - x02) ≤ (t - 1))) ∨ (¬ ((x23 - x03) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x03) + x23) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th61 t x02 x03 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause933 (t x02 x03 x23 : ℝ) : (((x02 + ((-1) * x03)) ≥ 0) ∨ ((x02 + ((-1) * x23)) ≤ (-1)) ∨ (¬ (x02 ≤ x03)) ∨ (¬ (x03 ≤ x23)) ∨ (¬ ((x23 - x02) ≥ 1)) ∨ (¬ ((x03 - x02) ≤ (t - 1))) ∨ (¬ ((x23 - x03) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x03)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x23)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th61 t x02 x03 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause934 (t x02 x03 x23 : ℝ) : (((x02 + ((-1) * x23)) ≤ (-1)) ∨ ((x02 + ((-1) * x23)) ≥ 1) ∨ (¬ (x02 ≤ x03)) ∨ (¬ (x03 ≤ x23)) ∨ (¬ ((x23 - x02) ≥ 1)) ∨ (¬ ((x03 - x02) ≤ (t - 1))) ∨ (¬ ((x23 - x03) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x23)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th61 t x02 x03 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause939 (t x02 x03 x23 : ℝ) : (((t + x02 + ((-1) * x03)) ≥ 1) ∨ ((x02 + ((-1) * x23)) ≥ 1) ∨ (¬ (x02 ≤ x03)) ∨ (¬ (x03 ≤ x23)) ∨ (¬ ((x23 - x02) ≥ 1)) ∨ (¬ ((x03 - x02) ≤ (t - 1))) ∨ (¬ ((x23 - x03) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x02 + ((-1) * x03)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th61 t x02 x03 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause942 (t x02 x03 x23 : ℝ) : (((t + x03 + ((-1) * x23)) ≥ 1) ∨ ((x03 + ((-1) * x23)) ≥ 0) ∨ (¬ (x02 ≤ x03)) ∨ (¬ (x03 ≤ x23)) ∨ (¬ ((x23 - x02) ≥ 1)) ∨ (¬ ((x03 - x02) ≤ (t - 1))) ∨ (¬ ((x23 - x03) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x03 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x23)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th61 t x02 x03 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause947 (t x02 x03 x23 : ℝ) : (((x02 + ((-1) * x03)) ≤ 0) ∨ ((x03 + ((-1) * x23)) ≥ 0) ∨ (¬ (x23 ≤ x03)) ∨ (¬ (x03 ≤ x02)) ∨ (¬ ((x02 - x23) ≥ 1)) ∨ (¬ ((x02 - x03) ≤ (t - 1))) ∨ (¬ ((x03 - x23) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x03)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x23)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th61 t x02 x03 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause949 (t x02 x03 x23 : ℝ) : (((x02 + ((-1) * x03)) ≤ 0) ∨ ((x02 + ((-1) * x23)) ≥ 1) ∨ (¬ (x23 ≤ x03)) ∨ (¬ (x03 ≤ x02)) ∨ (¬ ((x02 - x23) ≥ 1)) ∨ (¬ ((x02 - x03) ≤ (t - 1))) ∨ (¬ ((x03 - x23) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x03)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th61 t x02 x03 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause950 (t x02 x03 x23 : ℝ) : (((x02 + ((-1) * x03)) ≤ 0) ∨ ((t + ((-1) * x02) + x03) ≥ 1) ∨ (¬ (x23 ≤ x03)) ∨ (¬ (x03 ≤ x02)) ∨ (¬ ((x02 - x23) ≥ 1)) ∨ (¬ ((x02 - x03) ≤ (t - 1))) ∨ (¬ ((x03 - x23) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x03)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x02) + x03) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th61 t x02 x03 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause954 (t x02 x03 x23 : ℝ) : (((x03 + ((-1) * x23)) ≤ 0) ∨ ((x02 + ((-1) * x23)) ≥ 1) ∨ (¬ (x23 ≤ x03)) ∨ (¬ (x03 ≤ x02)) ∨ (¬ ((x02 - x23) ≥ 1)) ∨ (¬ ((x02 - x03) ≤ (t - 1))) ∨ (¬ ((x03 - x23) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th61 t x02 x03 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause955 (t x02 x03 x23 : ℝ) : (((x03 + ((-1) * x23)) ≤ 0) ∨ ((t + ((-1) * x02) + x03) ≥ 1) ∨ (¬ (x23 ≤ x03)) ∨ (¬ (x03 ≤ x02)) ∨ (¬ ((x02 - x23) ≥ 1)) ∨ (¬ ((x02 - x03) ≤ (t - 1))) ∨ (¬ ((x03 - x23) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x02) + x03) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th61 t x02 x03 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause956 (t x02 x03 x23 : ℝ) : (((x03 + ((-1) * x23)) ≤ 0) ∨ ((t + ((-1) * x03) + x23) ≥ 1) ∨ (¬ (x23 ≤ x03)) ∨ (¬ (x03 ≤ x02)) ∨ (¬ ((x02 - x23) ≥ 1)) ∨ (¬ ((x02 - x03) ≤ (t - 1))) ∨ (¬ ((x03 - x23) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x03) + x23) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th61 t x02 x03 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause958 (t x02 x03 x23 : ℝ) : (((x02 + ((-1) * x03)) ≥ 0) ∨ ((x02 + ((-1) * x23)) ≤ (-1)) ∨ (¬ (x23 ≤ x03)) ∨ (¬ (x03 ≤ x02)) ∨ (¬ ((x02 - x23) ≥ 1)) ∨ (¬ ((x02 - x03) ≤ (t - 1))) ∨ (¬ ((x03 - x23) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x03)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x23)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th61 t x02 x03 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause959 (t x02 x03 x23 : ℝ) : (((x02 + ((-1) * x23)) ≤ (-1)) ∨ ((x02 + ((-1) * x23)) ≥ 1) ∨ (¬ (x23 ≤ x03)) ∨ (¬ (x03 ≤ x02)) ∨ (¬ ((x02 - x23) ≥ 1)) ∨ (¬ ((x02 - x03) ≤ (t - 1))) ∨ (¬ ((x03 - x23) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x23)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th61 t x02 x03 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause964 (t x02 x03 x23 : ℝ) : (((t + x02 + ((-1) * x03)) ≥ 1) ∨ ((x02 + ((-1) * x23)) ≥ 1) ∨ (¬ (x23 ≤ x03)) ∨ (¬ (x03 ≤ x02)) ∨ (¬ ((x02 - x23) ≥ 1)) ∨ (¬ ((x02 - x03) ≤ (t - 1))) ∨ (¬ ((x03 - x23) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x02 + ((-1) * x03)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th61 t x02 x03 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause967 (t x02 x03 x23 : ℝ) : (((t + x03 + ((-1) * x23)) ≥ 1) ∨ ((x03 + ((-1) * x23)) ≥ 0) ∨ (¬ (x23 ≤ x03)) ∨ (¬ (x03 ≤ x02)) ∨ (¬ ((x02 - x23) ≥ 1)) ∨ (¬ ((x02 - x03) ≤ (t - 1))) ∨ (¬ ((x03 - x23) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x03 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x23)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th61 t x02 x03 x23
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1022 (t x02 x03 x23 : ℝ) (h : (((x02 ≤ x03) ∧ (x03 ≤ x23) ∧ ((x23 - x02) ≥ 1) ∧ ((x03 - x02) ≤ (t - 1)) ∧ ((x23 - x03) ≤ (t - 1))) ∨ ((x23 ≤ x03) ∧ (x03 ≤ x02) ∧ ((x02 - x23) ≥ 1) ∧ ((x02 - x03) ≤ (t - 1)) ∧ ((x03 - x23) ≤ (t - 1))))) : ((x02 ≤ x03) ∨ (x23 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x03) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x23 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1023 (t x02 x03 x23 : ℝ) (h : (((x02 ≤ x03) ∧ (x03 ≤ x23) ∧ ((x23 - x02) ≥ 1) ∧ ((x03 - x02) ≤ (t - 1)) ∧ ((x23 - x03) ≤ (t - 1))) ∨ ((x23 ≤ x03) ∧ (x03 ≤ x02) ∧ ((x02 - x23) ≥ 1) ∧ ((x02 - x03) ≤ (t - 1)) ∧ ((x03 - x23) ≤ (t - 1))))) : ((x02 ≤ x03) ∨ (x03 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x03) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x03 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1024 (t x02 x03 x23 : ℝ) (h : (((x02 ≤ x03) ∧ (x03 ≤ x23) ∧ ((x23 - x02) ≥ 1) ∧ ((x03 - x02) ≤ (t - 1)) ∧ ((x23 - x03) ≤ (t - 1))) ∨ ((x23 ≤ x03) ∧ (x03 ≤ x02) ∧ ((x02 - x23) ≥ 1) ∧ ((x02 - x03) ≤ (t - 1)) ∧ ((x03 - x23) ≤ (t - 1))))) : ((x02 ≤ x03) ∨ ((x02 - x23) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x03) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x23) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1025 (t x02 x03 x23 : ℝ) (h : (((x02 ≤ x03) ∧ (x03 ≤ x23) ∧ ((x23 - x02) ≥ 1) ∧ ((x03 - x02) ≤ (t - 1)) ∧ ((x23 - x03) ≤ (t - 1))) ∨ ((x23 ≤ x03) ∧ (x03 ≤ x02) ∧ ((x02 - x23) ≥ 1) ∧ ((x02 - x03) ≤ (t - 1)) ∧ ((x03 - x23) ≤ (t - 1))))) : ((x02 ≤ x03) ∨ ((x02 - x03) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x03) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x03) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1026 (t x02 x03 x23 : ℝ) (h : (((x02 ≤ x03) ∧ (x03 ≤ x23) ∧ ((x23 - x02) ≥ 1) ∧ ((x03 - x02) ≤ (t - 1)) ∧ ((x23 - x03) ≤ (t - 1))) ∨ ((x23 ≤ x03) ∧ (x03 ≤ x02) ∧ ((x02 - x23) ≥ 1) ∧ ((x02 - x03) ≤ (t - 1)) ∧ ((x03 - x23) ≤ (t - 1))))) : ((x02 ≤ x03) ∨ ((x03 - x23) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x03) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x23) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1027 (t x02 x03 x23 : ℝ) (h : (((x02 ≤ x03) ∧ (x03 ≤ x23) ∧ ((x23 - x02) ≥ 1) ∧ ((x03 - x02) ≤ (t - 1)) ∧ ((x23 - x03) ≤ (t - 1))) ∨ ((x23 ≤ x03) ∧ (x03 ≤ x02) ∧ ((x02 - x23) ≥ 1) ∧ ((x02 - x03) ≤ (t - 1)) ∧ ((x03 - x23) ≤ (t - 1))))) : ((x03 ≤ x23) ∨ (x23 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x23) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x23 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1028 (t x02 x03 x23 : ℝ) (h : (((x02 ≤ x03) ∧ (x03 ≤ x23) ∧ ((x23 - x02) ≥ 1) ∧ ((x03 - x02) ≤ (t - 1)) ∧ ((x23 - x03) ≤ (t - 1))) ∨ ((x23 ≤ x03) ∧ (x03 ≤ x02) ∧ ((x02 - x23) ≥ 1) ∧ ((x02 - x03) ≤ (t - 1)) ∧ ((x03 - x23) ≤ (t - 1))))) : ((x03 ≤ x23) ∨ (x03 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x23) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x03 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1029 (t x02 x03 x23 : ℝ) (h : (((x02 ≤ x03) ∧ (x03 ≤ x23) ∧ ((x23 - x02) ≥ 1) ∧ ((x03 - x02) ≤ (t - 1)) ∧ ((x23 - x03) ≤ (t - 1))) ∨ ((x23 ≤ x03) ∧ (x03 ≤ x02) ∧ ((x02 - x23) ≥ 1) ∧ ((x02 - x03) ≤ (t - 1)) ∧ ((x03 - x23) ≤ (t - 1))))) : ((x03 ≤ x23) ∨ ((x02 - x23) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x23) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x23) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1030 (t x02 x03 x23 : ℝ) (h : (((x02 ≤ x03) ∧ (x03 ≤ x23) ∧ ((x23 - x02) ≥ 1) ∧ ((x03 - x02) ≤ (t - 1)) ∧ ((x23 - x03) ≤ (t - 1))) ∨ ((x23 ≤ x03) ∧ (x03 ≤ x02) ∧ ((x02 - x23) ≥ 1) ∧ ((x02 - x03) ≤ (t - 1)) ∧ ((x03 - x23) ≤ (t - 1))))) : ((x03 ≤ x23) ∨ ((x02 - x03) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x23) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x03) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1031 (t x02 x03 x23 : ℝ) (h : (((x02 ≤ x03) ∧ (x03 ≤ x23) ∧ ((x23 - x02) ≥ 1) ∧ ((x03 - x02) ≤ (t - 1)) ∧ ((x23 - x03) ≤ (t - 1))) ∨ ((x23 ≤ x03) ∧ (x03 ≤ x02) ∧ ((x02 - x23) ≥ 1) ∧ ((x02 - x03) ≤ (t - 1)) ∧ ((x03 - x23) ≤ (t - 1))))) : ((x03 ≤ x23) ∨ ((x03 - x23) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x23) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x23) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1032 (t x02 x03 x23 : ℝ) (h : (((x02 ≤ x03) ∧ (x03 ≤ x23) ∧ ((x23 - x02) ≥ 1) ∧ ((x03 - x02) ≤ (t - 1)) ∧ ((x23 - x03) ≤ (t - 1))) ∨ ((x23 ≤ x03) ∧ (x03 ≤ x02) ∧ ((x02 - x23) ≥ 1) ∧ ((x02 - x03) ≤ (t - 1)) ∧ ((x03 - x23) ≤ (t - 1))))) : (((x23 - x02) ≥ 1) ∨ (x23 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x23 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1033 (t x02 x03 x23 : ℝ) (h : (((x02 ≤ x03) ∧ (x03 ≤ x23) ∧ ((x23 - x02) ≥ 1) ∧ ((x03 - x02) ≤ (t - 1)) ∧ ((x23 - x03) ≤ (t - 1))) ∨ ((x23 ≤ x03) ∧ (x03 ≤ x02) ∧ ((x02 - x23) ≥ 1) ∧ ((x02 - x03) ≤ (t - 1)) ∧ ((x03 - x23) ≤ (t - 1))))) : (((x23 - x02) ≥ 1) ∨ (x03 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x03 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1034 (t x02 x03 x23 : ℝ) (h : (((x02 ≤ x03) ∧ (x03 ≤ x23) ∧ ((x23 - x02) ≥ 1) ∧ ((x03 - x02) ≤ (t - 1)) ∧ ((x23 - x03) ≤ (t - 1))) ∨ ((x23 ≤ x03) ∧ (x03 ≤ x02) ∧ ((x02 - x23) ≥ 1) ∧ ((x02 - x03) ≤ (t - 1)) ∧ ((x03 - x23) ≤ (t - 1))))) : (((x23 - x02) ≥ 1) ∨ ((x02 - x23) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x23) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1035 (t x02 x03 x23 : ℝ) (h : (((x02 ≤ x03) ∧ (x03 ≤ x23) ∧ ((x23 - x02) ≥ 1) ∧ ((x03 - x02) ≤ (t - 1)) ∧ ((x23 - x03) ≤ (t - 1))) ∨ ((x23 ≤ x03) ∧ (x03 ≤ x02) ∧ ((x02 - x23) ≥ 1) ∧ ((x02 - x03) ≤ (t - 1)) ∧ ((x03 - x23) ≤ (t - 1))))) : (((x23 - x02) ≥ 1) ∨ ((x02 - x03) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x03) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1036 (t x02 x03 x23 : ℝ) (h : (((x02 ≤ x03) ∧ (x03 ≤ x23) ∧ ((x23 - x02) ≥ 1) ∧ ((x03 - x02) ≤ (t - 1)) ∧ ((x23 - x03) ≤ (t - 1))) ∨ ((x23 ≤ x03) ∧ (x03 ≤ x02) ∧ ((x02 - x23) ≥ 1) ∧ ((x02 - x03) ≤ (t - 1)) ∧ ((x03 - x23) ≤ (t - 1))))) : (((x23 - x02) ≥ 1) ∨ ((x03 - x23) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x23) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1037 (t x02 x03 x23 : ℝ) (h : (((x02 ≤ x03) ∧ (x03 ≤ x23) ∧ ((x23 - x02) ≥ 1) ∧ ((x03 - x02) ≤ (t - 1)) ∧ ((x23 - x03) ≤ (t - 1))) ∨ ((x23 ≤ x03) ∧ (x03 ≤ x02) ∧ ((x02 - x23) ≥ 1) ∧ ((x02 - x03) ≤ (t - 1)) ∧ ((x03 - x23) ≤ (t - 1))))) : (((x03 - x02) ≤ (t - 1)) ∨ (x23 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x23 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1038 (t x02 x03 x23 : ℝ) (h : (((x02 ≤ x03) ∧ (x03 ≤ x23) ∧ ((x23 - x02) ≥ 1) ∧ ((x03 - x02) ≤ (t - 1)) ∧ ((x23 - x03) ≤ (t - 1))) ∨ ((x23 ≤ x03) ∧ (x03 ≤ x02) ∧ ((x02 - x23) ≥ 1) ∧ ((x02 - x03) ≤ (t - 1)) ∧ ((x03 - x23) ≤ (t - 1))))) : (((x03 - x02) ≤ (t - 1)) ∨ (x03 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x03 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1039 (t x02 x03 x23 : ℝ) (h : (((x02 ≤ x03) ∧ (x03 ≤ x23) ∧ ((x23 - x02) ≥ 1) ∧ ((x03 - x02) ≤ (t - 1)) ∧ ((x23 - x03) ≤ (t - 1))) ∨ ((x23 ≤ x03) ∧ (x03 ≤ x02) ∧ ((x02 - x23) ≥ 1) ∧ ((x02 - x03) ≤ (t - 1)) ∧ ((x03 - x23) ≤ (t - 1))))) : (((x03 - x02) ≤ (t - 1)) ∨ ((x02 - x23) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x23) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1040 (t x02 x03 x23 : ℝ) (h : (((x02 ≤ x03) ∧ (x03 ≤ x23) ∧ ((x23 - x02) ≥ 1) ∧ ((x03 - x02) ≤ (t - 1)) ∧ ((x23 - x03) ≤ (t - 1))) ∨ ((x23 ≤ x03) ∧ (x03 ≤ x02) ∧ ((x02 - x23) ≥ 1) ∧ ((x02 - x03) ≤ (t - 1)) ∧ ((x03 - x23) ≤ (t - 1))))) : (((x03 - x02) ≤ (t - 1)) ∨ ((x02 - x03) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x03) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1041 (t x02 x03 x23 : ℝ) (h : (((x02 ≤ x03) ∧ (x03 ≤ x23) ∧ ((x23 - x02) ≥ 1) ∧ ((x03 - x02) ≤ (t - 1)) ∧ ((x23 - x03) ≤ (t - 1))) ∨ ((x23 ≤ x03) ∧ (x03 ≤ x02) ∧ ((x02 - x23) ≥ 1) ∧ ((x02 - x03) ≤ (t - 1)) ∧ ((x03 - x23) ≤ (t - 1))))) : (((x03 - x02) ≤ (t - 1)) ∨ ((x03 - x23) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x23) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1042 (t x02 x03 x23 : ℝ) (h : (((x02 ≤ x03) ∧ (x03 ≤ x23) ∧ ((x23 - x02) ≥ 1) ∧ ((x03 - x02) ≤ (t - 1)) ∧ ((x23 - x03) ≤ (t - 1))) ∨ ((x23 ≤ x03) ∧ (x03 ≤ x02) ∧ ((x02 - x23) ≥ 1) ∧ ((x02 - x03) ≤ (t - 1)) ∧ ((x03 - x23) ≤ (t - 1))))) : (((x23 - x03) ≤ (t - 1)) ∨ (x23 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x23 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1043 (t x02 x03 x23 : ℝ) (h : (((x02 ≤ x03) ∧ (x03 ≤ x23) ∧ ((x23 - x02) ≥ 1) ∧ ((x03 - x02) ≤ (t - 1)) ∧ ((x23 - x03) ≤ (t - 1))) ∨ ((x23 ≤ x03) ∧ (x03 ≤ x02) ∧ ((x02 - x23) ≥ 1) ∧ ((x02 - x03) ≤ (t - 1)) ∧ ((x03 - x23) ≤ (t - 1))))) : (((x23 - x03) ≤ (t - 1)) ∨ (x03 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x03 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1044 (t x02 x03 x23 : ℝ) (h : (((x02 ≤ x03) ∧ (x03 ≤ x23) ∧ ((x23 - x02) ≥ 1) ∧ ((x03 - x02) ≤ (t - 1)) ∧ ((x23 - x03) ≤ (t - 1))) ∨ ((x23 ≤ x03) ∧ (x03 ≤ x02) ∧ ((x02 - x23) ≥ 1) ∧ ((x02 - x03) ≤ (t - 1)) ∧ ((x03 - x23) ≤ (t - 1))))) : (((x23 - x03) ≤ (t - 1)) ∨ ((x02 - x23) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x23) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1045 (t x02 x03 x23 : ℝ) (h : (((x02 ≤ x03) ∧ (x03 ≤ x23) ∧ ((x23 - x02) ≥ 1) ∧ ((x03 - x02) ≤ (t - 1)) ∧ ((x23 - x03) ≤ (t - 1))) ∨ ((x23 ≤ x03) ∧ (x03 ≤ x02) ∧ ((x02 - x23) ≥ 1) ∧ ((x02 - x03) ≤ (t - 1)) ∧ ((x03 - x23) ≤ (t - 1))))) : (((x23 - x03) ≤ (t - 1)) ∨ ((x02 - x03) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x03) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1046 (t x02 x03 x23 : ℝ) (h : (((x02 ≤ x03) ∧ (x03 ≤ x23) ∧ ((x23 - x02) ≥ 1) ∧ ((x03 - x02) ≤ (t - 1)) ∧ ((x23 - x03) ≤ (t - 1))) ∨ ((x23 ≤ x03) ∧ (x03 ≤ x02) ∧ ((x02 - x23) ≥ 1) ∧ ((x02 - x03) ≤ (t - 1)) ∧ ((x03 - x23) ≤ (t - 1))))) : (((x23 - x03) ≤ (t - 1)) ∨ ((x03 - x23) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x23) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1049 (t x03 x04 x34 : ℝ) : (((x03 + ((-1) * x34)) ≥ 1) ∨ ((x03 + ((-1) * x04)) ≤ 0) ∨ (¬ (x03 ≤ x04)) ∨ (¬ (x04 ≤ x34)) ∨ (¬ ((x34 - x03) ≥ 1)) ∨ (¬ ((x04 - x03) ≤ (t - 1))) ∨ (¬ ((x34 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x04)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th64 t x03 x04 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1053 (t x03 x04 x34 : ℝ) : (((x04 + ((-1) * x34)) ≤ 0) ∨ ((x03 + ((-1) * x04)) ≥ 0) ∨ (¬ (x03 ≤ x04)) ∨ (¬ (x04 ≤ x34)) ∨ (¬ ((x34 - x03) ≥ 1)) ∨ (¬ ((x04 - x03) ≤ (t - 1))) ∨ (¬ ((x34 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x04)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th64 t x03 x04 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1054 (t x03 x04 x34 : ℝ) : (((x03 + ((-1) * x34)) ≥ 1) ∨ ((x04 + ((-1) * x34)) ≤ 0) ∨ (¬ (x03 ≤ x04)) ∨ (¬ (x04 ≤ x34)) ∨ (¬ ((x34 - x03) ≥ 1)) ∨ (¬ ((x04 - x03) ≤ (t - 1))) ∨ (¬ ((x34 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th64 t x03 x04 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1056 (t x03 x04 x34 : ℝ) : (((x04 + ((-1) * x34)) ≤ 0) ∨ ((t + ((-1) * x04) + x34) ≥ 1) ∨ (¬ (x03 ≤ x04)) ∨ (¬ (x04 ≤ x34)) ∨ (¬ ((x34 - x03) ≥ 1)) ∨ (¬ ((x04 - x03) ≤ (t - 1))) ∨ (¬ ((x34 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x04) + x34) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th64 t x03 x04 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1057 (t x03 x04 x34 : ℝ) : (((x03 + ((-1) * x34)) ≤ (-1)) ∨ ((x04 + ((-1) * x34)) ≥ 0) ∨ (¬ (x03 ≤ x04)) ∨ (¬ (x04 ≤ x34)) ∨ (¬ ((x34 - x03) ≥ 1)) ∨ (¬ ((x04 - x03) ≤ (t - 1))) ∨ (¬ ((x34 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x34)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th64 t x03 x04 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1058 (t x03 x04 x34 : ℝ) : (((x03 + ((-1) * x34)) ≤ (-1)) ∨ ((x03 + ((-1) * x04)) ≥ 0) ∨ (¬ (x03 ≤ x04)) ∨ (¬ (x04 ≤ x34)) ∨ (¬ ((x34 - x03) ≥ 1)) ∨ (¬ ((x04 - x03) ≤ (t - 1))) ∨ (¬ ((x34 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x04)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th64 t x03 x04 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1059 (t x03 x04 x34 : ℝ) : (((x03 + ((-1) * x34)) ≤ (-1)) ∨ ((x03 + ((-1) * x34)) ≥ 1) ∨ (¬ (x03 ≤ x04)) ∨ (¬ (x04 ≤ x34)) ∨ (¬ ((x34 - x03) ≥ 1)) ∨ (¬ ((x04 - x03) ≤ (t - 1))) ∨ (¬ ((x34 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th64 t x03 x04 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1061 (t x03 x04 x34 : ℝ) : (((x03 + ((-1) * x34)) ≤ (-1)) ∨ ((t + ((-1) * x04) + x34) ≥ 1) ∨ (¬ (x03 ≤ x04)) ∨ (¬ (x04 ≤ x34)) ∨ (¬ ((x34 - x03) ≥ 1)) ∨ (¬ ((x04 - x03) ≤ (t - 1))) ∨ (¬ ((x34 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x04) + x34) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th64 t x03 x04 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1064 (t x03 x04 x34 : ℝ) : (((x03 + ((-1) * x34)) ≥ 1) ∨ ((t + x03 + ((-1) * x04)) ≥ 1) ∨ (¬ (x03 ≤ x04)) ∨ (¬ (x04 ≤ x34)) ∨ (¬ ((x34 - x03) ≥ 1)) ∨ (¬ ((x04 - x03) ≤ (t - 1))) ∨ (¬ ((x34 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x03 + ((-1) * x04)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th64 t x03 x04 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1069 (t x03 x04 x34 : ℝ) : (((x03 + ((-1) * x34)) ≥ 1) ∨ ((t + x04 + ((-1) * x34)) ≥ 1) ∨ (¬ (x03 ≤ x04)) ∨ (¬ (x04 ≤ x34)) ∨ (¬ ((x34 - x03) ≥ 1)) ∨ (¬ ((x04 - x03) ≤ (t - 1))) ∨ (¬ ((x34 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x04 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th64 t x03 x04 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1072 (t x03 x04 x34 : ℝ) : (((x03 + ((-1) * x04)) ≤ 0) ∨ ((x04 + ((-1) * x34)) ≥ 0) ∨ (¬ (x34 ≤ x04)) ∨ (¬ (x04 ≤ x03)) ∨ (¬ ((x03 - x34) ≥ 1)) ∨ (¬ ((x03 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x04)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x34)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th64 t x03 x04 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1074 (t x03 x04 x34 : ℝ) : (((x03 + ((-1) * x34)) ≥ 1) ∨ ((x03 + ((-1) * x04)) ≤ 0) ∨ (¬ (x34 ≤ x04)) ∨ (¬ (x04 ≤ x03)) ∨ (¬ ((x03 - x34) ≥ 1)) ∨ (¬ ((x03 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x04)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th64 t x03 x04 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1078 (t x03 x04 x34 : ℝ) : (((x04 + ((-1) * x34)) ≤ 0) ∨ ((x03 + ((-1) * x04)) ≥ 0) ∨ (¬ (x34 ≤ x04)) ∨ (¬ (x04 ≤ x03)) ∨ (¬ ((x03 - x34) ≥ 1)) ∨ (¬ ((x03 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x04)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th64 t x03 x04 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1079 (t x03 x04 x34 : ℝ) : (((x03 + ((-1) * x34)) ≥ 1) ∨ ((x04 + ((-1) * x34)) ≤ 0) ∨ (¬ (x34 ≤ x04)) ∨ (¬ (x04 ≤ x03)) ∨ (¬ ((x03 - x34) ≥ 1)) ∨ (¬ ((x03 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th64 t x03 x04 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1081 (t x03 x04 x34 : ℝ) : (((x04 + ((-1) * x34)) ≤ 0) ∨ ((t + ((-1) * x04) + x34) ≥ 1) ∨ (¬ (x34 ≤ x04)) ∨ (¬ (x04 ≤ x03)) ∨ (¬ ((x03 - x34) ≥ 1)) ∨ (¬ ((x03 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x04) + x34) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th64 t x03 x04 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1082 (t x03 x04 x34 : ℝ) : (((x03 + ((-1) * x34)) ≤ (-1)) ∨ ((x04 + ((-1) * x34)) ≥ 0) ∨ (¬ (x34 ≤ x04)) ∨ (¬ (x04 ≤ x03)) ∨ (¬ ((x03 - x34) ≥ 1)) ∨ (¬ ((x03 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x34)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th64 t x03 x04 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1083 (t x03 x04 x34 : ℝ) : (((x03 + ((-1) * x34)) ≤ (-1)) ∨ ((x03 + ((-1) * x04)) ≥ 0) ∨ (¬ (x34 ≤ x04)) ∨ (¬ (x04 ≤ x03)) ∨ (¬ ((x03 - x34) ≥ 1)) ∨ (¬ ((x03 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x04)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th64 t x03 x04 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1084 (t x03 x04 x34 : ℝ) : (((x03 + ((-1) * x34)) ≤ (-1)) ∨ ((x03 + ((-1) * x34)) ≥ 1) ∨ (¬ (x34 ≤ x04)) ∨ (¬ (x04 ≤ x03)) ∨ (¬ ((x03 - x34) ≥ 1)) ∨ (¬ ((x03 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th64 t x03 x04 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1089 (t x03 x04 x34 : ℝ) : (((x03 + ((-1) * x34)) ≥ 1) ∨ ((t + x03 + ((-1) * x04)) ≥ 1) ∨ (¬ (x34 ≤ x04)) ∨ (¬ (x04 ≤ x03)) ∨ (¬ ((x03 - x34) ≥ 1)) ∨ (¬ ((x03 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x03 + ((-1) * x04)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th64 t x03 x04 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1092 (t x03 x04 x34 : ℝ) : (((t + x04 + ((-1) * x34)) ≥ 1) ∨ ((x04 + ((-1) * x34)) ≥ 0) ∨ (¬ (x34 ≤ x04)) ∨ (¬ (x04 ≤ x03)) ∨ (¬ ((x03 - x34) ≥ 1)) ∨ (¬ ((x03 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x04 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x34)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th64 t x03 x04 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1094 (t x03 x04 x34 : ℝ) : (((x03 + ((-1) * x34)) ≥ 1) ∨ ((t + x04 + ((-1) * x34)) ≥ 1) ∨ (¬ (x34 ≤ x04)) ∨ (¬ (x04 ≤ x03)) ∨ (¬ ((x03 - x34) ≥ 1)) ∨ (¬ ((x03 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x34) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x04 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th64 t x03 x04 x34
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1147 (t x03 x04 x34 : ℝ) (h : (((x03 ≤ x04) ∧ (x04 ≤ x34) ∧ ((x34 - x03) ≥ 1) ∧ ((x04 - x03) ≤ (t - 1)) ∧ ((x34 - x04) ≤ (t - 1))) ∨ ((x34 ≤ x04) ∧ (x04 ≤ x03) ∧ ((x03 - x34) ≥ 1) ∧ ((x03 - x04) ≤ (t - 1)) ∧ ((x04 - x34) ≤ (t - 1))))) : ((x03 ≤ x04) ∨ (x34 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x04) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x34 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1148 (t x03 x04 x34 : ℝ) (h : (((x03 ≤ x04) ∧ (x04 ≤ x34) ∧ ((x34 - x03) ≥ 1) ∧ ((x04 - x03) ≤ (t - 1)) ∧ ((x34 - x04) ≤ (t - 1))) ∨ ((x34 ≤ x04) ∧ (x04 ≤ x03) ∧ ((x03 - x34) ≥ 1) ∧ ((x03 - x04) ≤ (t - 1)) ∧ ((x04 - x34) ≤ (t - 1))))) : ((x03 ≤ x04) ∨ (x04 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x04) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x04 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1149 (t x03 x04 x34 : ℝ) (h : (((x03 ≤ x04) ∧ (x04 ≤ x34) ∧ ((x34 - x03) ≥ 1) ∧ ((x04 - x03) ≤ (t - 1)) ∧ ((x34 - x04) ≤ (t - 1))) ∨ ((x34 ≤ x04) ∧ (x04 ≤ x03) ∧ ((x03 - x34) ≥ 1) ∧ ((x03 - x04) ≤ (t - 1)) ∧ ((x04 - x34) ≤ (t - 1))))) : ((x03 ≤ x04) ∨ ((x03 - x34) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x04) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x34) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1150 (t x03 x04 x34 : ℝ) (h : (((x03 ≤ x04) ∧ (x04 ≤ x34) ∧ ((x34 - x03) ≥ 1) ∧ ((x04 - x03) ≤ (t - 1)) ∧ ((x34 - x04) ≤ (t - 1))) ∨ ((x34 ≤ x04) ∧ (x04 ≤ x03) ∧ ((x03 - x34) ≥ 1) ∧ ((x03 - x04) ≤ (t - 1)) ∧ ((x04 - x34) ≤ (t - 1))))) : ((x03 ≤ x04) ∨ ((x03 - x04) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x04) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x04) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1151 (t x03 x04 x34 : ℝ) (h : (((x03 ≤ x04) ∧ (x04 ≤ x34) ∧ ((x34 - x03) ≥ 1) ∧ ((x04 - x03) ≤ (t - 1)) ∧ ((x34 - x04) ≤ (t - 1))) ∨ ((x34 ≤ x04) ∧ (x04 ≤ x03) ∧ ((x03 - x34) ≥ 1) ∧ ((x03 - x04) ≤ (t - 1)) ∧ ((x04 - x34) ≤ (t - 1))))) : ((x03 ≤ x04) ∨ ((x04 - x34) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x04) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x34) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1152 (t x03 x04 x34 : ℝ) (h : (((x03 ≤ x04) ∧ (x04 ≤ x34) ∧ ((x34 - x03) ≥ 1) ∧ ((x04 - x03) ≤ (t - 1)) ∧ ((x34 - x04) ≤ (t - 1))) ∨ ((x34 ≤ x04) ∧ (x04 ≤ x03) ∧ ((x03 - x34) ≥ 1) ∧ ((x03 - x04) ≤ (t - 1)) ∧ ((x04 - x34) ≤ (t - 1))))) : ((x04 ≤ x34) ∨ (x34 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x34) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x34 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1153 (t x03 x04 x34 : ℝ) (h : (((x03 ≤ x04) ∧ (x04 ≤ x34) ∧ ((x34 - x03) ≥ 1) ∧ ((x04 - x03) ≤ (t - 1)) ∧ ((x34 - x04) ≤ (t - 1))) ∨ ((x34 ≤ x04) ∧ (x04 ≤ x03) ∧ ((x03 - x34) ≥ 1) ∧ ((x03 - x04) ≤ (t - 1)) ∧ ((x04 - x34) ≤ (t - 1))))) : ((x04 ≤ x34) ∨ (x04 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x34) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x04 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1154 (t x03 x04 x34 : ℝ) (h : (((x03 ≤ x04) ∧ (x04 ≤ x34) ∧ ((x34 - x03) ≥ 1) ∧ ((x04 - x03) ≤ (t - 1)) ∧ ((x34 - x04) ≤ (t - 1))) ∨ ((x34 ≤ x04) ∧ (x04 ≤ x03) ∧ ((x03 - x34) ≥ 1) ∧ ((x03 - x04) ≤ (t - 1)) ∧ ((x04 - x34) ≤ (t - 1))))) : ((x04 ≤ x34) ∨ ((x03 - x34) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x34) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x34) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1155 (t x03 x04 x34 : ℝ) (h : (((x03 ≤ x04) ∧ (x04 ≤ x34) ∧ ((x34 - x03) ≥ 1) ∧ ((x04 - x03) ≤ (t - 1)) ∧ ((x34 - x04) ≤ (t - 1))) ∨ ((x34 ≤ x04) ∧ (x04 ≤ x03) ∧ ((x03 - x34) ≥ 1) ∧ ((x03 - x04) ≤ (t - 1)) ∧ ((x04 - x34) ≤ (t - 1))))) : ((x04 ≤ x34) ∨ ((x03 - x04) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x34) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x04) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1156 (t x03 x04 x34 : ℝ) (h : (((x03 ≤ x04) ∧ (x04 ≤ x34) ∧ ((x34 - x03) ≥ 1) ∧ ((x04 - x03) ≤ (t - 1)) ∧ ((x34 - x04) ≤ (t - 1))) ∨ ((x34 ≤ x04) ∧ (x04 ≤ x03) ∧ ((x03 - x34) ≥ 1) ∧ ((x03 - x04) ≤ (t - 1)) ∧ ((x04 - x34) ≤ (t - 1))))) : ((x04 ≤ x34) ∨ ((x04 - x34) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x34) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x34) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1157 (t x03 x04 x34 : ℝ) (h : (((x03 ≤ x04) ∧ (x04 ≤ x34) ∧ ((x34 - x03) ≥ 1) ∧ ((x04 - x03) ≤ (t - 1)) ∧ ((x34 - x04) ≤ (t - 1))) ∨ ((x34 ≤ x04) ∧ (x04 ≤ x03) ∧ ((x03 - x34) ≥ 1) ∧ ((x03 - x04) ≤ (t - 1)) ∧ ((x04 - x34) ≤ (t - 1))))) : (((x34 - x03) ≥ 1) ∨ (x34 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x34 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1158 (t x03 x04 x34 : ℝ) (h : (((x03 ≤ x04) ∧ (x04 ≤ x34) ∧ ((x34 - x03) ≥ 1) ∧ ((x04 - x03) ≤ (t - 1)) ∧ ((x34 - x04) ≤ (t - 1))) ∨ ((x34 ≤ x04) ∧ (x04 ≤ x03) ∧ ((x03 - x34) ≥ 1) ∧ ((x03 - x04) ≤ (t - 1)) ∧ ((x04 - x34) ≤ (t - 1))))) : (((x34 - x03) ≥ 1) ∨ (x04 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x04 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1159 (t x03 x04 x34 : ℝ) (h : (((x03 ≤ x04) ∧ (x04 ≤ x34) ∧ ((x34 - x03) ≥ 1) ∧ ((x04 - x03) ≤ (t - 1)) ∧ ((x34 - x04) ≤ (t - 1))) ∨ ((x34 ≤ x04) ∧ (x04 ≤ x03) ∧ ((x03 - x34) ≥ 1) ∧ ((x03 - x04) ≤ (t - 1)) ∧ ((x04 - x34) ≤ (t - 1))))) : (((x34 - x03) ≥ 1) ∨ ((x03 - x34) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x34) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1160 (t x03 x04 x34 : ℝ) (h : (((x03 ≤ x04) ∧ (x04 ≤ x34) ∧ ((x34 - x03) ≥ 1) ∧ ((x04 - x03) ≤ (t - 1)) ∧ ((x34 - x04) ≤ (t - 1))) ∨ ((x34 ≤ x04) ∧ (x04 ≤ x03) ∧ ((x03 - x34) ≥ 1) ∧ ((x03 - x04) ≤ (t - 1)) ∧ ((x04 - x34) ≤ (t - 1))))) : (((x34 - x03) ≥ 1) ∨ ((x03 - x04) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x04) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1161 (t x03 x04 x34 : ℝ) (h : (((x03 ≤ x04) ∧ (x04 ≤ x34) ∧ ((x34 - x03) ≥ 1) ∧ ((x04 - x03) ≤ (t - 1)) ∧ ((x34 - x04) ≤ (t - 1))) ∨ ((x34 ≤ x04) ∧ (x04 ≤ x03) ∧ ((x03 - x34) ≥ 1) ∧ ((x03 - x04) ≤ (t - 1)) ∧ ((x04 - x34) ≤ (t - 1))))) : (((x34 - x03) ≥ 1) ∨ ((x04 - x34) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x34) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1162 (t x03 x04 x34 : ℝ) (h : (((x03 ≤ x04) ∧ (x04 ≤ x34) ∧ ((x34 - x03) ≥ 1) ∧ ((x04 - x03) ≤ (t - 1)) ∧ ((x34 - x04) ≤ (t - 1))) ∨ ((x34 ≤ x04) ∧ (x04 ≤ x03) ∧ ((x03 - x34) ≥ 1) ∧ ((x03 - x04) ≤ (t - 1)) ∧ ((x04 - x34) ≤ (t - 1))))) : (((x04 - x03) ≤ (t - 1)) ∨ (x34 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x34 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1163 (t x03 x04 x34 : ℝ) (h : (((x03 ≤ x04) ∧ (x04 ≤ x34) ∧ ((x34 - x03) ≥ 1) ∧ ((x04 - x03) ≤ (t - 1)) ∧ ((x34 - x04) ≤ (t - 1))) ∨ ((x34 ≤ x04) ∧ (x04 ≤ x03) ∧ ((x03 - x34) ≥ 1) ∧ ((x03 - x04) ≤ (t - 1)) ∧ ((x04 - x34) ≤ (t - 1))))) : (((x04 - x03) ≤ (t - 1)) ∨ (x04 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x04 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1164 (t x03 x04 x34 : ℝ) (h : (((x03 ≤ x04) ∧ (x04 ≤ x34) ∧ ((x34 - x03) ≥ 1) ∧ ((x04 - x03) ≤ (t - 1)) ∧ ((x34 - x04) ≤ (t - 1))) ∨ ((x34 ≤ x04) ∧ (x04 ≤ x03) ∧ ((x03 - x34) ≥ 1) ∧ ((x03 - x04) ≤ (t - 1)) ∧ ((x04 - x34) ≤ (t - 1))))) : (((x04 - x03) ≤ (t - 1)) ∨ ((x03 - x34) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x34) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1165 (t x03 x04 x34 : ℝ) (h : (((x03 ≤ x04) ∧ (x04 ≤ x34) ∧ ((x34 - x03) ≥ 1) ∧ ((x04 - x03) ≤ (t - 1)) ∧ ((x34 - x04) ≤ (t - 1))) ∨ ((x34 ≤ x04) ∧ (x04 ≤ x03) ∧ ((x03 - x34) ≥ 1) ∧ ((x03 - x04) ≤ (t - 1)) ∧ ((x04 - x34) ≤ (t - 1))))) : (((x04 - x03) ≤ (t - 1)) ∨ ((x03 - x04) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x04) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1166 (t x03 x04 x34 : ℝ) (h : (((x03 ≤ x04) ∧ (x04 ≤ x34) ∧ ((x34 - x03) ≥ 1) ∧ ((x04 - x03) ≤ (t - 1)) ∧ ((x34 - x04) ≤ (t - 1))) ∨ ((x34 ≤ x04) ∧ (x04 ≤ x03) ∧ ((x03 - x34) ≥ 1) ∧ ((x03 - x04) ≤ (t - 1)) ∧ ((x04 - x34) ≤ (t - 1))))) : (((x04 - x03) ≤ (t - 1)) ∨ ((x04 - x34) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x34) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1167 (t x03 x04 x34 : ℝ) (h : (((x03 ≤ x04) ∧ (x04 ≤ x34) ∧ ((x34 - x03) ≥ 1) ∧ ((x04 - x03) ≤ (t - 1)) ∧ ((x34 - x04) ≤ (t - 1))) ∨ ((x34 ≤ x04) ∧ (x04 ≤ x03) ∧ ((x03 - x34) ≥ 1) ∧ ((x03 - x04) ≤ (t - 1)) ∧ ((x04 - x34) ≤ (t - 1))))) : (((x34 - x04) ≤ (t - 1)) ∨ (x34 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x34 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1168 (t x03 x04 x34 : ℝ) (h : (((x03 ≤ x04) ∧ (x04 ≤ x34) ∧ ((x34 - x03) ≥ 1) ∧ ((x04 - x03) ≤ (t - 1)) ∧ ((x34 - x04) ≤ (t - 1))) ∨ ((x34 ≤ x04) ∧ (x04 ≤ x03) ∧ ((x03 - x34) ≥ 1) ∧ ((x03 - x04) ≤ (t - 1)) ∧ ((x04 - x34) ≤ (t - 1))))) : (((x34 - x04) ≤ (t - 1)) ∨ (x04 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x04 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1169 (t x03 x04 x34 : ℝ) (h : (((x03 ≤ x04) ∧ (x04 ≤ x34) ∧ ((x34 - x03) ≥ 1) ∧ ((x04 - x03) ≤ (t - 1)) ∧ ((x34 - x04) ≤ (t - 1))) ∨ ((x34 ≤ x04) ∧ (x04 ≤ x03) ∧ ((x03 - x34) ≥ 1) ∧ ((x03 - x04) ≤ (t - 1)) ∧ ((x04 - x34) ≤ (t - 1))))) : (((x34 - x04) ≤ (t - 1)) ∨ ((x03 - x34) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x34) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1170 (t x03 x04 x34 : ℝ) (h : (((x03 ≤ x04) ∧ (x04 ≤ x34) ∧ ((x34 - x03) ≥ 1) ∧ ((x04 - x03) ≤ (t - 1)) ∧ ((x34 - x04) ≤ (t - 1))) ∨ ((x34 ≤ x04) ∧ (x04 ≤ x03) ∧ ((x03 - x34) ≥ 1) ∧ ((x03 - x04) ≤ (t - 1)) ∧ ((x04 - x34) ≤ (t - 1))))) : (((x34 - x04) ≤ (t - 1)) ∨ ((x03 - x04) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x04) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1171 (t x03 x04 x34 : ℝ) (h : (((x03 ≤ x04) ∧ (x04 ≤ x34) ∧ ((x34 - x03) ≥ 1) ∧ ((x04 - x03) ≤ (t - 1)) ∧ ((x34 - x04) ≤ (t - 1))) ∨ ((x34 ≤ x04) ∧ (x04 ≤ x03) ∧ ((x03 - x34) ≥ 1) ∧ ((x03 - x04) ≤ (t - 1)) ∧ ((x04 - x34) ≤ (t - 1))))) : (((x34 - x04) ≤ (t - 1)) ∨ ((x04 - x34) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x34) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1172 (t x03 x13 x23 x34 x35 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + x13 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1)))) := by
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
  have u3 : ((t + x13 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th67 t x03 x13 x23 x34 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u5 u3))))))) h

theorem clause1173 (t x12 x13 x23 : ℝ) : ((¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ ((t + x13 + ((-1) * x23)) ≥ 1) ∨ (¬ (x13 ≥ 0)) ∨ ((t + ((-1) * x12)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + x13 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th68 t x12 x13 x23
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u0 u2))))) h

theorem clause1174 (t x12 : ℝ) : ((¬ ((t + ((-1) * x12)) ≤ 0)) ∨ (t ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x12) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th69 t x12
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause1176 (t x12 : ℝ) : ((¬ (t ≤ x12)) ∨ (¬ (x12 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x12 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th70 t x12
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause1178 (t x12 : ℝ) (h : (x12 < t)) : ((x12 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 < t) := fun hh => hn hh
  exact u0 h

theorem clause1179 (x02 x25 : ℝ) : ((¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th73 x02 x25
  exact (fun hh => (Or.elim hh (fun hh => hh u0) (fun zz => ((fun hh => hh u1) zz)))) h

theorem clause1180 (t x02 x05 x25 : ℝ) : (((x02 + ((-1) * x05)) ≤ 0) ∨ ((x05 + ((-1) * x25)) ≥ 0) ∨ (¬ (x02 ≤ x05)) ∨ (¬ (x05 ≤ x25)) ∨ (¬ ((x25 - x02) ≥ 1)) ∨ (¬ ((x05 - x02) ≤ (t - 1))) ∨ (¬ ((x25 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x05)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x25)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1181 (t x02 x05 x25 : ℝ) : (((x02 + ((-1) * x05)) ≤ 0) ∨ ((x02 + ((-1) * x05)) ≥ 0) ∨ (¬ (x02 ≤ x05)) ∨ (¬ (x05 ≤ x25)) ∨ (¬ ((x25 - x02) ≥ 1)) ∨ (¬ ((x05 - x02) ≤ (t - 1))) ∨ (¬ ((x25 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x05)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x05)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1182 (t x02 x05 x25 : ℝ) : (((x02 + ((-1) * x25)) ≥ 1) ∨ ((x02 + ((-1) * x05)) ≤ 0) ∨ (¬ (x02 ≤ x05)) ∨ (¬ (x05 ≤ x25)) ∨ (¬ ((x25 - x02) ≥ 1)) ∨ (¬ ((x05 - x02) ≤ (t - 1))) ∨ (¬ ((x25 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x05)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1183 (t x02 x05 x25 : ℝ) : (((x02 + ((-1) * x05)) ≤ 0) ∨ ((t + ((-1) * x02) + x05) ≥ 1) ∨ (¬ (x02 ≤ x05)) ∨ (¬ (x05 ≤ x25)) ∨ (¬ ((x25 - x02) ≥ 1)) ∨ (¬ ((x05 - x02) ≤ (t - 1))) ∨ (¬ ((x25 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x05)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x02) + x05) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1184 (t x02 x05 x25 : ℝ) : (((x02 + ((-1) * x05)) ≤ 0) ∨ ((t + ((-1) * x05) + x25) ≥ 1) ∨ (¬ (x02 ≤ x05)) ∨ (¬ (x05 ≤ x25)) ∨ (¬ ((x25 - x02) ≥ 1)) ∨ (¬ ((x05 - x02) ≤ (t - 1))) ∨ (¬ ((x25 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x05)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x05) + x25) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1187 (t x02 x05 x25 : ℝ) : (((x05 + ((-1) * x25)) ≤ 0) ∨ ((x02 + ((-1) * x25)) ≥ 1) ∨ (¬ (x02 ≤ x05)) ∨ (¬ (x05 ≤ x25)) ∨ (¬ ((x25 - x02) ≥ 1)) ∨ (¬ ((x05 - x02) ≤ (t - 1))) ∨ (¬ ((x25 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x25)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1188 (t x02 x05 x25 : ℝ) : (((x05 + ((-1) * x25)) ≤ 0) ∨ ((t + ((-1) * x02) + x05) ≥ 1) ∨ (¬ (x02 ≤ x05)) ∨ (¬ (x05 ≤ x25)) ∨ (¬ ((x25 - x02) ≥ 1)) ∨ (¬ ((x05 - x02) ≤ (t - 1))) ∨ (¬ ((x25 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x25)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x02) + x05) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1189 (t x02 x05 x25 : ℝ) : (((x05 + ((-1) * x25)) ≤ 0) ∨ ((t + ((-1) * x05) + x25) ≥ 1) ∨ (¬ (x02 ≤ x05)) ∨ (¬ (x05 ≤ x25)) ∨ (¬ ((x25 - x02) ≥ 1)) ∨ (¬ ((x05 - x02) ≤ (t - 1))) ∨ (¬ ((x25 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x25)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x05) + x25) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1190 (t x02 x05 x25 : ℝ) : (((x02 + ((-1) * x25)) ≤ (-1)) ∨ ((x05 + ((-1) * x25)) ≥ 0) ∨ (¬ (x02 ≤ x05)) ∨ (¬ (x05 ≤ x25)) ∨ (¬ ((x25 - x02) ≥ 1)) ∨ (¬ ((x05 - x02) ≤ (t - 1))) ∨ (¬ ((x25 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x25)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x25)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1191 (t x02 x05 x25 : ℝ) : (((x02 + ((-1) * x25)) ≤ (-1)) ∨ ((x02 + ((-1) * x05)) ≥ 0) ∨ (¬ (x02 ≤ x05)) ∨ (¬ (x05 ≤ x25)) ∨ (¬ ((x25 - x02) ≥ 1)) ∨ (¬ ((x05 - x02) ≤ (t - 1))) ∨ (¬ ((x25 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x25)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x05)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1192 (t x02 x05 x25 : ℝ) : (((x02 + ((-1) * x25)) ≤ (-1)) ∨ ((x02 + ((-1) * x25)) ≥ 1) ∨ (¬ (x02 ≤ x05)) ∨ (¬ (x05 ≤ x25)) ∨ (¬ ((x25 - x02) ≥ 1)) ∨ (¬ ((x05 - x02) ≤ (t - 1))) ∨ (¬ ((x25 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x25)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1196 (t x02 x05 x25 : ℝ) : (((t + x02 + ((-1) * x05)) ≥ 1) ∨ ((x02 + ((-1) * x05)) ≥ 0) ∨ (¬ (x02 ≤ x05)) ∨ (¬ (x05 ≤ x25)) ∨ (¬ ((x25 - x02) ≥ 1)) ∨ (¬ ((x05 - x02) ≤ (t - 1))) ∨ (¬ ((x25 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x02 + ((-1) * x05)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x05)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1197 (t x02 x05 x25 : ℝ) : (((x02 + ((-1) * x25)) ≥ 1) ∨ ((t + x02 + ((-1) * x05)) ≥ 1) ∨ (¬ (x02 ≤ x05)) ∨ (¬ (x05 ≤ x25)) ∨ (¬ ((x25 - x02) ≥ 1)) ∨ (¬ ((x05 - x02) ≤ (t - 1))) ∨ (¬ ((x25 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x02 + ((-1) * x05)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1200 (t x02 x05 x25 : ℝ) : (((t + x05 + ((-1) * x25)) ≥ 1) ∨ ((x05 + ((-1) * x25)) ≥ 0) ∨ (¬ (x02 ≤ x05)) ∨ (¬ (x05 ≤ x25)) ∨ (¬ ((x25 - x02) ≥ 1)) ∨ (¬ ((x05 - x02) ≤ (t - 1))) ∨ (¬ ((x25 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x05 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x25)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1205 (t x02 x05 x25 : ℝ) : (((x02 + ((-1) * x05)) ≤ 0) ∨ ((x05 + ((-1) * x25)) ≥ 0) ∨ (¬ (x25 ≤ x05)) ∨ (¬ (x05 ≤ x02)) ∨ (¬ ((x02 - x25) ≥ 1)) ∨ (¬ ((x02 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x05)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x25)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1206 (t x02 x05 x25 : ℝ) : (((x02 + ((-1) * x05)) ≤ 0) ∨ ((x02 + ((-1) * x05)) ≥ 0) ∨ (¬ (x25 ≤ x05)) ∨ (¬ (x05 ≤ x02)) ∨ (¬ ((x02 - x25) ≥ 1)) ∨ (¬ ((x02 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x05)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x05)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1207 (t x02 x05 x25 : ℝ) : (((x02 + ((-1) * x25)) ≥ 1) ∨ ((x02 + ((-1) * x05)) ≤ 0) ∨ (¬ (x25 ≤ x05)) ∨ (¬ (x05 ≤ x02)) ∨ (¬ ((x02 - x25) ≥ 1)) ∨ (¬ ((x02 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x05)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1208 (t x02 x05 x25 : ℝ) : (((x02 + ((-1) * x05)) ≤ 0) ∨ ((t + ((-1) * x02) + x05) ≥ 1) ∨ (¬ (x25 ≤ x05)) ∨ (¬ (x05 ≤ x02)) ∨ (¬ ((x02 - x25) ≥ 1)) ∨ (¬ ((x02 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x05)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x02) + x05) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1209 (t x02 x05 x25 : ℝ) : (((x02 + ((-1) * x05)) ≤ 0) ∨ ((t + ((-1) * x05) + x25) ≥ 1) ∨ (¬ (x25 ≤ x05)) ∨ (¬ (x05 ≤ x02)) ∨ (¬ ((x02 - x25) ≥ 1)) ∨ (¬ ((x02 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x05)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x05) + x25) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1212 (t x02 x05 x25 : ℝ) : (((x05 + ((-1) * x25)) ≤ 0) ∨ ((x02 + ((-1) * x25)) ≥ 1) ∨ (¬ (x25 ≤ x05)) ∨ (¬ (x05 ≤ x02)) ∨ (¬ ((x02 - x25) ≥ 1)) ∨ (¬ ((x02 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x25)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1213 (t x02 x05 x25 : ℝ) : (((x05 + ((-1) * x25)) ≤ 0) ∨ ((t + ((-1) * x02) + x05) ≥ 1) ∨ (¬ (x25 ≤ x05)) ∨ (¬ (x05 ≤ x02)) ∨ (¬ ((x02 - x25) ≥ 1)) ∨ (¬ ((x02 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x25)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x02) + x05) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1214 (t x02 x05 x25 : ℝ) : (((x05 + ((-1) * x25)) ≤ 0) ∨ ((t + ((-1) * x05) + x25) ≥ 1) ∨ (¬ (x25 ≤ x05)) ∨ (¬ (x05 ≤ x02)) ∨ (¬ ((x02 - x25) ≥ 1)) ∨ (¬ ((x02 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x25)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x05) + x25) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1215 (t x02 x05 x25 : ℝ) : (((x02 + ((-1) * x25)) ≤ (-1)) ∨ ((x05 + ((-1) * x25)) ≥ 0) ∨ (¬ (x25 ≤ x05)) ∨ (¬ (x05 ≤ x02)) ∨ (¬ ((x02 - x25) ≥ 1)) ∨ (¬ ((x02 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x25)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x25)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1216 (t x02 x05 x25 : ℝ) : (((x02 + ((-1) * x25)) ≤ (-1)) ∨ ((x02 + ((-1) * x05)) ≥ 0) ∨ (¬ (x25 ≤ x05)) ∨ (¬ (x05 ≤ x02)) ∨ (¬ ((x02 - x25) ≥ 1)) ∨ (¬ ((x02 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x25)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x05)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1217 (t x02 x05 x25 : ℝ) : (((x02 + ((-1) * x25)) ≤ (-1)) ∨ ((x02 + ((-1) * x25)) ≥ 1) ∨ (¬ (x25 ≤ x05)) ∨ (¬ (x05 ≤ x02)) ∨ (¬ ((x02 - x25) ≥ 1)) ∨ (¬ ((x02 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x25)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1222 (t x02 x05 x25 : ℝ) : (((x02 + ((-1) * x25)) ≥ 1) ∨ ((t + x02 + ((-1) * x05)) ≥ 1) ∨ (¬ (x25 ≤ x05)) ∨ (¬ (x05 ≤ x02)) ∨ (¬ ((x02 - x25) ≥ 1)) ∨ (¬ ((x02 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x02 + ((-1) * x05)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1225 (t x02 x05 x25 : ℝ) : (((t + x05 + ((-1) * x25)) ≥ 1) ∨ ((x05 + ((-1) * x25)) ≥ 0) ∨ (¬ (x25 ≤ x05)) ∨ (¬ (x05 ≤ x02)) ∨ (¬ ((x02 - x25) ≥ 1)) ∨ (¬ ((x02 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x05 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x25)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th75 t x02 x05 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1280 (t x02 x05 x25 : ℝ) (h : (((x02 ≤ x05) ∧ (x05 ≤ x25) ∧ ((x25 - x02) ≥ 1) ∧ ((x05 - x02) ≤ (t - 1)) ∧ ((x25 - x05) ≤ (t - 1))) ∨ ((x25 ≤ x05) ∧ (x05 ≤ x02) ∧ ((x02 - x25) ≥ 1) ∧ ((x02 - x05) ≤ (t - 1)) ∧ ((x05 - x25) ≤ (t - 1))))) : ((x02 ≤ x05) ∨ (x25 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x05) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x25 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1281 (t x02 x05 x25 : ℝ) (h : (((x02 ≤ x05) ∧ (x05 ≤ x25) ∧ ((x25 - x02) ≥ 1) ∧ ((x05 - x02) ≤ (t - 1)) ∧ ((x25 - x05) ≤ (t - 1))) ∨ ((x25 ≤ x05) ∧ (x05 ≤ x02) ∧ ((x02 - x25) ≥ 1) ∧ ((x02 - x05) ≤ (t - 1)) ∧ ((x05 - x25) ≤ (t - 1))))) : ((x02 ≤ x05) ∨ (x05 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x05) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x05 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1282 (t x02 x05 x25 : ℝ) (h : (((x02 ≤ x05) ∧ (x05 ≤ x25) ∧ ((x25 - x02) ≥ 1) ∧ ((x05 - x02) ≤ (t - 1)) ∧ ((x25 - x05) ≤ (t - 1))) ∨ ((x25 ≤ x05) ∧ (x05 ≤ x02) ∧ ((x02 - x25) ≥ 1) ∧ ((x02 - x05) ≤ (t - 1)) ∧ ((x05 - x25) ≤ (t - 1))))) : ((x02 ≤ x05) ∨ ((x02 - x25) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x05) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x25) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1283 (t x02 x05 x25 : ℝ) (h : (((x02 ≤ x05) ∧ (x05 ≤ x25) ∧ ((x25 - x02) ≥ 1) ∧ ((x05 - x02) ≤ (t - 1)) ∧ ((x25 - x05) ≤ (t - 1))) ∨ ((x25 ≤ x05) ∧ (x05 ≤ x02) ∧ ((x02 - x25) ≥ 1) ∧ ((x02 - x05) ≤ (t - 1)) ∧ ((x05 - x25) ≤ (t - 1))))) : ((x02 ≤ x05) ∨ ((x02 - x05) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x05) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x05) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1284 (t x02 x05 x25 : ℝ) (h : (((x02 ≤ x05) ∧ (x05 ≤ x25) ∧ ((x25 - x02) ≥ 1) ∧ ((x05 - x02) ≤ (t - 1)) ∧ ((x25 - x05) ≤ (t - 1))) ∨ ((x25 ≤ x05) ∧ (x05 ≤ x02) ∧ ((x02 - x25) ≥ 1) ∧ ((x02 - x05) ≤ (t - 1)) ∧ ((x05 - x25) ≤ (t - 1))))) : ((x02 ≤ x05) ∨ ((x05 - x25) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x05) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x25) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1285 (t x02 x05 x25 : ℝ) (h : (((x02 ≤ x05) ∧ (x05 ≤ x25) ∧ ((x25 - x02) ≥ 1) ∧ ((x05 - x02) ≤ (t - 1)) ∧ ((x25 - x05) ≤ (t - 1))) ∨ ((x25 ≤ x05) ∧ (x05 ≤ x02) ∧ ((x02 - x25) ≥ 1) ∧ ((x02 - x05) ≤ (t - 1)) ∧ ((x05 - x25) ≤ (t - 1))))) : ((x05 ≤ x25) ∨ (x25 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x25) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x25 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1286 (t x02 x05 x25 : ℝ) (h : (((x02 ≤ x05) ∧ (x05 ≤ x25) ∧ ((x25 - x02) ≥ 1) ∧ ((x05 - x02) ≤ (t - 1)) ∧ ((x25 - x05) ≤ (t - 1))) ∨ ((x25 ≤ x05) ∧ (x05 ≤ x02) ∧ ((x02 - x25) ≥ 1) ∧ ((x02 - x05) ≤ (t - 1)) ∧ ((x05 - x25) ≤ (t - 1))))) : ((x05 ≤ x25) ∨ (x05 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x25) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x05 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

#print axioms clause1286
end NineCNFDirectTrial
