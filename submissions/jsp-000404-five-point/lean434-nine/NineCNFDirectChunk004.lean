import NineTheoryTrial

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineCNFDirectTrial

theorem clause5446 (t x12 x15 x25 : ℝ) (h : (((x12 ≤ x15) ∧ (x15 ≤ x25) ∧ ((x25 - x12) ≥ 1) ∧ ((x15 - x12) ≤ (t - 1)) ∧ ((x25 - x15) ≤ (t - 1))) ∨ ((x25 ≤ x15) ∧ (x15 ≤ x12) ∧ ((x12 - x25) ≥ 1) ∧ ((x12 - x15) ≤ (t - 1)) ∧ ((x15 - x25) ≤ (t - 1))))) : (((x25 - x12) ≥ 1) ∨ ((x12 - x15) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x12) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x15) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5447 (t x12 x15 x25 : ℝ) (h : (((x12 ≤ x15) ∧ (x15 ≤ x25) ∧ ((x25 - x12) ≥ 1) ∧ ((x15 - x12) ≤ (t - 1)) ∧ ((x25 - x15) ≤ (t - 1))) ∨ ((x25 ≤ x15) ∧ (x15 ≤ x12) ∧ ((x12 - x25) ≥ 1) ∧ ((x12 - x15) ≤ (t - 1)) ∧ ((x15 - x25) ≤ (t - 1))))) : (((x25 - x12) ≥ 1) ∨ ((x15 - x25) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x12) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x25) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5448 (t x12 x15 x25 : ℝ) (h : (((x12 ≤ x15) ∧ (x15 ≤ x25) ∧ ((x25 - x12) ≥ 1) ∧ ((x15 - x12) ≤ (t - 1)) ∧ ((x25 - x15) ≤ (t - 1))) ∨ ((x25 ≤ x15) ∧ (x15 ≤ x12) ∧ ((x12 - x25) ≥ 1) ∧ ((x12 - x15) ≤ (t - 1)) ∧ ((x15 - x25) ≤ (t - 1))))) : (((x15 - x12) ≤ (t - 1)) ∨ (x25 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 - x12) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x25 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5449 (t x12 x15 x25 : ℝ) (h : (((x12 ≤ x15) ∧ (x15 ≤ x25) ∧ ((x25 - x12) ≥ 1) ∧ ((x15 - x12) ≤ (t - 1)) ∧ ((x25 - x15) ≤ (t - 1))) ∨ ((x25 ≤ x15) ∧ (x15 ≤ x12) ∧ ((x12 - x25) ≥ 1) ∧ ((x12 - x15) ≤ (t - 1)) ∧ ((x15 - x25) ≤ (t - 1))))) : (((x15 - x12) ≤ (t - 1)) ∨ (x15 ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 - x12) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x15 ≤ x12) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5450 (t x12 x15 x25 : ℝ) (h : (((x12 ≤ x15) ∧ (x15 ≤ x25) ∧ ((x25 - x12) ≥ 1) ∧ ((x15 - x12) ≤ (t - 1)) ∧ ((x25 - x15) ≤ (t - 1))) ∨ ((x25 ≤ x15) ∧ (x15 ≤ x12) ∧ ((x12 - x25) ≥ 1) ∧ ((x12 - x15) ≤ (t - 1)) ∧ ((x15 - x25) ≤ (t - 1))))) : (((x15 - x12) ≤ (t - 1)) ∨ ((x12 - x25) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 - x12) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x25) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5451 (t x12 x15 x25 : ℝ) (h : (((x12 ≤ x15) ∧ (x15 ≤ x25) ∧ ((x25 - x12) ≥ 1) ∧ ((x15 - x12) ≤ (t - 1)) ∧ ((x25 - x15) ≤ (t - 1))) ∨ ((x25 ≤ x15) ∧ (x15 ≤ x12) ∧ ((x12 - x25) ≥ 1) ∧ ((x12 - x15) ≤ (t - 1)) ∧ ((x15 - x25) ≤ (t - 1))))) : (((x15 - x12) ≤ (t - 1)) ∨ ((x12 - x15) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 - x12) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x15) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5452 (t x12 x15 x25 : ℝ) (h : (((x12 ≤ x15) ∧ (x15 ≤ x25) ∧ ((x25 - x12) ≥ 1) ∧ ((x15 - x12) ≤ (t - 1)) ∧ ((x25 - x15) ≤ (t - 1))) ∨ ((x25 ≤ x15) ∧ (x15 ≤ x12) ∧ ((x12 - x25) ≥ 1) ∧ ((x12 - x15) ≤ (t - 1)) ∧ ((x15 - x25) ≤ (t - 1))))) : (((x15 - x12) ≤ (t - 1)) ∨ ((x15 - x25) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 - x12) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x25) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5453 (t x12 x15 x25 : ℝ) (h : (((x12 ≤ x15) ∧ (x15 ≤ x25) ∧ ((x25 - x12) ≥ 1) ∧ ((x15 - x12) ≤ (t - 1)) ∧ ((x25 - x15) ≤ (t - 1))) ∨ ((x25 ≤ x15) ∧ (x15 ≤ x12) ∧ ((x12 - x25) ≥ 1) ∧ ((x12 - x15) ≤ (t - 1)) ∧ ((x15 - x25) ≤ (t - 1))))) : (((x25 - x15) ≤ (t - 1)) ∨ (x25 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x25 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5454 (t x12 x15 x25 : ℝ) (h : (((x12 ≤ x15) ∧ (x15 ≤ x25) ∧ ((x25 - x12) ≥ 1) ∧ ((x15 - x12) ≤ (t - 1)) ∧ ((x25 - x15) ≤ (t - 1))) ∨ ((x25 ≤ x15) ∧ (x15 ≤ x12) ∧ ((x12 - x25) ≥ 1) ∧ ((x12 - x15) ≤ (t - 1)) ∧ ((x15 - x25) ≤ (t - 1))))) : (((x25 - x15) ≤ (t - 1)) ∨ (x15 ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x15 ≤ x12) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5455 (t x12 x15 x25 : ℝ) (h : (((x12 ≤ x15) ∧ (x15 ≤ x25) ∧ ((x25 - x12) ≥ 1) ∧ ((x15 - x12) ≤ (t - 1)) ∧ ((x25 - x15) ≤ (t - 1))) ∨ ((x25 ≤ x15) ∧ (x15 ≤ x12) ∧ ((x12 - x25) ≥ 1) ∧ ((x12 - x15) ≤ (t - 1)) ∧ ((x15 - x25) ≤ (t - 1))))) : (((x25 - x15) ≤ (t - 1)) ∨ ((x12 - x25) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x25) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5456 (t x12 x15 x25 : ℝ) (h : (((x12 ≤ x15) ∧ (x15 ≤ x25) ∧ ((x25 - x12) ≥ 1) ∧ ((x15 - x12) ≤ (t - 1)) ∧ ((x25 - x15) ≤ (t - 1))) ∨ ((x25 ≤ x15) ∧ (x15 ≤ x12) ∧ ((x12 - x25) ≥ 1) ∧ ((x12 - x15) ≤ (t - 1)) ∧ ((x15 - x25) ≤ (t - 1))))) : (((x25 - x15) ≤ (t - 1)) ∨ ((x12 - x15) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x15) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5457 (t x12 x15 x25 : ℝ) (h : (((x12 ≤ x15) ∧ (x15 ≤ x25) ∧ ((x25 - x12) ≥ 1) ∧ ((x15 - x12) ≤ (t - 1)) ∧ ((x25 - x15) ≤ (t - 1))) ∨ ((x25 ≤ x15) ∧ (x15 ≤ x12) ∧ ((x12 - x25) ≥ 1) ∧ ((x12 - x15) ≤ (t - 1)) ∧ ((x15 - x25) ≤ (t - 1))))) : (((x25 - x15) ≤ (t - 1)) ∨ ((x15 - x25) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x25) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5458 (x03 x23 x35 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x23)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th316 x03 x23 x35
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u2 u0))) h

theorem clause5459 (t x02 x23 x24 x25 x26 x35 x46 x56 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x23) + x24) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x25 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x23) + x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x46) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x35 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th317 t x02 x23 x24 x25 x26 x35 x46 x56 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u0 (And.intro u8 (And.intro u2 (And.intro u7 (And.intro u9 (And.intro u6 (And.intro u5 u4))))))))))) h

theorem clause5471 (t x35 x38 x58 : ℝ) : (((x35 + ((-1) * x58)) ≤ (-1)) ∨ ((x35 + ((-1) * x38)) ≥ 0) ∨ (¬ (x35 ≤ x38)) ∨ (¬ (x38 ≤ x58)) ∨ (¬ ((x58 - x35) ≥ 1)) ∨ (¬ ((x38 - x35) ≤ (t - 1))) ∨ (¬ ((x58 - x38) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x58)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x38)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x58 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x38 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th319 t x35 x38 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5472 (t x35 x38 x58 : ℝ) : (((x35 + ((-1) * x58)) ≥ 1) ∨ ((x35 + ((-1) * x58)) ≤ (-1)) ∨ (¬ (x35 ≤ x38)) ∨ (¬ (x38 ≤ x58)) ∨ (¬ ((x58 - x35) ≥ 1)) ∨ (¬ ((x38 - x35) ≤ (t - 1))) ∨ (¬ ((x58 - x38) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x58)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x58)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x58 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x38 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th319 t x35 x38 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5496 (t x35 x38 x58 : ℝ) : (((x35 + ((-1) * x58)) ≤ (-1)) ∨ ((x35 + ((-1) * x38)) ≥ 0) ∨ (¬ (x58 ≤ x38)) ∨ (¬ (x38 ≤ x35)) ∨ (¬ ((x35 - x58) ≥ 1)) ∨ (¬ ((x35 - x38) ≤ (t - 1))) ∨ (¬ ((x38 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x58)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x38)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x58 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x58) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x38 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th319 t x35 x38 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5497 (t x35 x38 x58 : ℝ) : (((x35 + ((-1) * x58)) ≥ 1) ∨ ((x35 + ((-1) * x58)) ≤ (-1)) ∨ (¬ (x58 ≤ x38)) ∨ (¬ (x38 ≤ x35)) ∨ (¬ ((x35 - x58) ≥ 1)) ∨ (¬ ((x35 - x38) ≤ (t - 1))) ∨ (¬ ((x38 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x58)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x58)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x58 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x58) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x38 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th319 t x35 x38 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5560 (t x35 x38 x58 : ℝ) (h : (((x35 ≤ x38) ∧ (x38 ≤ x58) ∧ ((x58 - x35) ≥ 1) ∧ ((x38 - x35) ≤ (t - 1)) ∧ ((x58 - x38) ≤ (t - 1))) ∨ ((x58 ≤ x38) ∧ (x38 ≤ x35) ∧ ((x35 - x58) ≥ 1) ∧ ((x35 - x38) ≤ (t - 1)) ∧ ((x38 - x58) ≤ (t - 1))))) : ((x35 ≤ x38) ∨ (x58 ≤ x38)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x35 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x38) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5561 (t x35 x38 x58 : ℝ) (h : (((x35 ≤ x38) ∧ (x38 ≤ x58) ∧ ((x58 - x35) ≥ 1) ∧ ((x38 - x35) ≤ (t - 1)) ∧ ((x58 - x38) ≤ (t - 1))) ∨ ((x58 ≤ x38) ∧ (x38 ≤ x35) ∧ ((x35 - x58) ≥ 1) ∧ ((x35 - x38) ≤ (t - 1)) ∧ ((x38 - x58) ≤ (t - 1))))) : ((x35 ≤ x38) ∨ (x38 ≤ x35)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x35 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x35) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5562 (t x35 x38 x58 : ℝ) (h : (((x35 ≤ x38) ∧ (x38 ≤ x58) ∧ ((x58 - x35) ≥ 1) ∧ ((x38 - x35) ≤ (t - 1)) ∧ ((x58 - x38) ≤ (t - 1))) ∨ ((x58 ≤ x38) ∧ (x38 ≤ x35) ∧ ((x35 - x58) ≥ 1) ∧ ((x35 - x38) ≤ (t - 1)) ∧ ((x38 - x58) ≤ (t - 1))))) : ((x35 ≤ x38) ∨ ((x35 - x58) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x35 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x58) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5563 (t x35 x38 x58 : ℝ) (h : (((x35 ≤ x38) ∧ (x38 ≤ x58) ∧ ((x58 - x35) ≥ 1) ∧ ((x38 - x35) ≤ (t - 1)) ∧ ((x58 - x38) ≤ (t - 1))) ∨ ((x58 ≤ x38) ∧ (x38 ≤ x35) ∧ ((x35 - x58) ≥ 1) ∧ ((x35 - x38) ≤ (t - 1)) ∧ ((x38 - x58) ≤ (t - 1))))) : ((x35 ≤ x38) ∨ ((x35 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x35 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5564 (t x35 x38 x58 : ℝ) (h : (((x35 ≤ x38) ∧ (x38 ≤ x58) ∧ ((x58 - x35) ≥ 1) ∧ ((x38 - x35) ≤ (t - 1)) ∧ ((x58 - x38) ≤ (t - 1))) ∨ ((x58 ≤ x38) ∧ (x38 ≤ x35) ∧ ((x35 - x58) ≥ 1) ∧ ((x35 - x38) ≤ (t - 1)) ∧ ((x38 - x58) ≤ (t - 1))))) : ((x35 ≤ x38) ∨ ((x38 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x35 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5565 (t x35 x38 x58 : ℝ) (h : (((x35 ≤ x38) ∧ (x38 ≤ x58) ∧ ((x58 - x35) ≥ 1) ∧ ((x38 - x35) ≤ (t - 1)) ∧ ((x58 - x38) ≤ (t - 1))) ∨ ((x58 ≤ x38) ∧ (x38 ≤ x35) ∧ ((x35 - x58) ≥ 1) ∧ ((x35 - x38) ≤ (t - 1)) ∧ ((x38 - x58) ≤ (t - 1))))) : ((x38 ≤ x58) ∨ (x58 ≤ x38)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x38 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x38) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5566 (t x35 x38 x58 : ℝ) (h : (((x35 ≤ x38) ∧ (x38 ≤ x58) ∧ ((x58 - x35) ≥ 1) ∧ ((x38 - x35) ≤ (t - 1)) ∧ ((x58 - x38) ≤ (t - 1))) ∨ ((x58 ≤ x38) ∧ (x38 ≤ x35) ∧ ((x35 - x58) ≥ 1) ∧ ((x35 - x38) ≤ (t - 1)) ∧ ((x38 - x58) ≤ (t - 1))))) : ((x38 ≤ x58) ∨ (x38 ≤ x35)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x38 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x35) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5567 (t x35 x38 x58 : ℝ) (h : (((x35 ≤ x38) ∧ (x38 ≤ x58) ∧ ((x58 - x35) ≥ 1) ∧ ((x38 - x35) ≤ (t - 1)) ∧ ((x58 - x38) ≤ (t - 1))) ∨ ((x58 ≤ x38) ∧ (x38 ≤ x35) ∧ ((x35 - x58) ≥ 1) ∧ ((x35 - x38) ≤ (t - 1)) ∧ ((x38 - x58) ≤ (t - 1))))) : ((x38 ≤ x58) ∨ ((x35 - x58) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x38 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x58) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5568 (t x35 x38 x58 : ℝ) (h : (((x35 ≤ x38) ∧ (x38 ≤ x58) ∧ ((x58 - x35) ≥ 1) ∧ ((x38 - x35) ≤ (t - 1)) ∧ ((x58 - x38) ≤ (t - 1))) ∨ ((x58 ≤ x38) ∧ (x38 ≤ x35) ∧ ((x35 - x58) ≥ 1) ∧ ((x35 - x38) ≤ (t - 1)) ∧ ((x38 - x58) ≤ (t - 1))))) : ((x38 ≤ x58) ∨ ((x35 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x38 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5569 (t x35 x38 x58 : ℝ) (h : (((x35 ≤ x38) ∧ (x38 ≤ x58) ∧ ((x58 - x35) ≥ 1) ∧ ((x38 - x35) ≤ (t - 1)) ∧ ((x58 - x38) ≤ (t - 1))) ∨ ((x58 ≤ x38) ∧ (x38 ≤ x35) ∧ ((x35 - x58) ≥ 1) ∧ ((x35 - x38) ≤ (t - 1)) ∧ ((x38 - x58) ≤ (t - 1))))) : ((x38 ≤ x58) ∨ ((x38 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x38 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5570 (t x35 x38 x58 : ℝ) (h : (((x35 ≤ x38) ∧ (x38 ≤ x58) ∧ ((x58 - x35) ≥ 1) ∧ ((x38 - x35) ≤ (t - 1)) ∧ ((x58 - x38) ≤ (t - 1))) ∨ ((x58 ≤ x38) ∧ (x38 ≤ x35) ∧ ((x35 - x58) ≥ 1) ∧ ((x35 - x38) ≤ (t - 1)) ∧ ((x38 - x58) ≤ (t - 1))))) : (((x58 - x35) ≥ 1) ∨ (x58 ≤ x38)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x35) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x38) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5571 (t x35 x38 x58 : ℝ) (h : (((x35 ≤ x38) ∧ (x38 ≤ x58) ∧ ((x58 - x35) ≥ 1) ∧ ((x38 - x35) ≤ (t - 1)) ∧ ((x58 - x38) ≤ (t - 1))) ∨ ((x58 ≤ x38) ∧ (x38 ≤ x35) ∧ ((x35 - x58) ≥ 1) ∧ ((x35 - x38) ≤ (t - 1)) ∧ ((x38 - x58) ≤ (t - 1))))) : (((x58 - x35) ≥ 1) ∨ (x38 ≤ x35)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x35) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x35) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5572 (t x35 x38 x58 : ℝ) (h : (((x35 ≤ x38) ∧ (x38 ≤ x58) ∧ ((x58 - x35) ≥ 1) ∧ ((x38 - x35) ≤ (t - 1)) ∧ ((x58 - x38) ≤ (t - 1))) ∨ ((x58 ≤ x38) ∧ (x38 ≤ x35) ∧ ((x35 - x58) ≥ 1) ∧ ((x35 - x38) ≤ (t - 1)) ∧ ((x38 - x58) ≤ (t - 1))))) : (((x58 - x35) ≥ 1) ∨ ((x35 - x58) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x35) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x58) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5573 (t x35 x38 x58 : ℝ) (h : (((x35 ≤ x38) ∧ (x38 ≤ x58) ∧ ((x58 - x35) ≥ 1) ∧ ((x38 - x35) ≤ (t - 1)) ∧ ((x58 - x38) ≤ (t - 1))) ∨ ((x58 ≤ x38) ∧ (x38 ≤ x35) ∧ ((x35 - x58) ≥ 1) ∧ ((x35 - x38) ≤ (t - 1)) ∧ ((x38 - x58) ≤ (t - 1))))) : (((x58 - x35) ≥ 1) ∨ ((x35 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x35) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5574 (t x35 x38 x58 : ℝ) (h : (((x35 ≤ x38) ∧ (x38 ≤ x58) ∧ ((x58 - x35) ≥ 1) ∧ ((x38 - x35) ≤ (t - 1)) ∧ ((x58 - x38) ≤ (t - 1))) ∨ ((x58 ≤ x38) ∧ (x38 ≤ x35) ∧ ((x35 - x58) ≥ 1) ∧ ((x35 - x38) ≤ (t - 1)) ∧ ((x38 - x58) ≤ (t - 1))))) : (((x58 - x35) ≥ 1) ∨ ((x38 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x35) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5575 (t x35 x38 x58 : ℝ) (h : (((x35 ≤ x38) ∧ (x38 ≤ x58) ∧ ((x58 - x35) ≥ 1) ∧ ((x38 - x35) ≤ (t - 1)) ∧ ((x58 - x38) ≤ (t - 1))) ∨ ((x58 ≤ x38) ∧ (x38 ≤ x35) ∧ ((x35 - x58) ≥ 1) ∧ ((x35 - x38) ≤ (t - 1)) ∧ ((x38 - x58) ≤ (t - 1))))) : (((x38 - x35) ≤ (t - 1)) ∨ (x58 ≤ x38)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x35) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x38) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5576 (t x35 x38 x58 : ℝ) (h : (((x35 ≤ x38) ∧ (x38 ≤ x58) ∧ ((x58 - x35) ≥ 1) ∧ ((x38 - x35) ≤ (t - 1)) ∧ ((x58 - x38) ≤ (t - 1))) ∨ ((x58 ≤ x38) ∧ (x38 ≤ x35) ∧ ((x35 - x58) ≥ 1) ∧ ((x35 - x38) ≤ (t - 1)) ∧ ((x38 - x58) ≤ (t - 1))))) : (((x38 - x35) ≤ (t - 1)) ∨ (x38 ≤ x35)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x35) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x35) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5577 (t x35 x38 x58 : ℝ) (h : (((x35 ≤ x38) ∧ (x38 ≤ x58) ∧ ((x58 - x35) ≥ 1) ∧ ((x38 - x35) ≤ (t - 1)) ∧ ((x58 - x38) ≤ (t - 1))) ∨ ((x58 ≤ x38) ∧ (x38 ≤ x35) ∧ ((x35 - x58) ≥ 1) ∧ ((x35 - x38) ≤ (t - 1)) ∧ ((x38 - x58) ≤ (t - 1))))) : (((x38 - x35) ≤ (t - 1)) ∨ ((x35 - x58) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x35) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x58) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5578 (t x35 x38 x58 : ℝ) (h : (((x35 ≤ x38) ∧ (x38 ≤ x58) ∧ ((x58 - x35) ≥ 1) ∧ ((x38 - x35) ≤ (t - 1)) ∧ ((x58 - x38) ≤ (t - 1))) ∨ ((x58 ≤ x38) ∧ (x38 ≤ x35) ∧ ((x35 - x58) ≥ 1) ∧ ((x35 - x38) ≤ (t - 1)) ∧ ((x38 - x58) ≤ (t - 1))))) : (((x38 - x35) ≤ (t - 1)) ∨ ((x35 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x35) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5579 (t x35 x38 x58 : ℝ) (h : (((x35 ≤ x38) ∧ (x38 ≤ x58) ∧ ((x58 - x35) ≥ 1) ∧ ((x38 - x35) ≤ (t - 1)) ∧ ((x58 - x38) ≤ (t - 1))) ∨ ((x58 ≤ x38) ∧ (x38 ≤ x35) ∧ ((x35 - x58) ≥ 1) ∧ ((x35 - x38) ≤ (t - 1)) ∧ ((x38 - x58) ≤ (t - 1))))) : (((x38 - x35) ≤ (t - 1)) ∨ ((x38 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x35) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5580 (t x35 x38 x58 : ℝ) (h : (((x35 ≤ x38) ∧ (x38 ≤ x58) ∧ ((x58 - x35) ≥ 1) ∧ ((x38 - x35) ≤ (t - 1)) ∧ ((x58 - x38) ≤ (t - 1))) ∨ ((x58 ≤ x38) ∧ (x38 ≤ x35) ∧ ((x35 - x58) ≥ 1) ∧ ((x35 - x38) ≤ (t - 1)) ∧ ((x38 - x58) ≤ (t - 1))))) : (((x58 - x38) ≤ (t - 1)) ∨ (x58 ≤ x38)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x38) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x38) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5581 (t x35 x38 x58 : ℝ) (h : (((x35 ≤ x38) ∧ (x38 ≤ x58) ∧ ((x58 - x35) ≥ 1) ∧ ((x38 - x35) ≤ (t - 1)) ∧ ((x58 - x38) ≤ (t - 1))) ∨ ((x58 ≤ x38) ∧ (x38 ≤ x35) ∧ ((x35 - x58) ≥ 1) ∧ ((x35 - x38) ≤ (t - 1)) ∧ ((x38 - x58) ≤ (t - 1))))) : (((x58 - x38) ≤ (t - 1)) ∨ (x38 ≤ x35)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x38) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x35) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5582 (t x35 x38 x58 : ℝ) (h : (((x35 ≤ x38) ∧ (x38 ≤ x58) ∧ ((x58 - x35) ≥ 1) ∧ ((x38 - x35) ≤ (t - 1)) ∧ ((x58 - x38) ≤ (t - 1))) ∨ ((x58 ≤ x38) ∧ (x38 ≤ x35) ∧ ((x35 - x58) ≥ 1) ∧ ((x35 - x38) ≤ (t - 1)) ∧ ((x38 - x58) ≤ (t - 1))))) : (((x58 - x38) ≤ (t - 1)) ∨ ((x35 - x58) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x38) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x58) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5583 (t x35 x38 x58 : ℝ) (h : (((x35 ≤ x38) ∧ (x38 ≤ x58) ∧ ((x58 - x35) ≥ 1) ∧ ((x38 - x35) ≤ (t - 1)) ∧ ((x58 - x38) ≤ (t - 1))) ∨ ((x58 ≤ x38) ∧ (x38 ≤ x35) ∧ ((x35 - x58) ≥ 1) ∧ ((x35 - x38) ≤ (t - 1)) ∧ ((x38 - x58) ≤ (t - 1))))) : (((x58 - x38) ≤ (t - 1)) ∨ ((x35 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x38) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5584 (t x35 x38 x58 : ℝ) (h : (((x35 ≤ x38) ∧ (x38 ≤ x58) ∧ ((x58 - x35) ≥ 1) ∧ ((x38 - x35) ≤ (t - 1)) ∧ ((x58 - x38) ≤ (t - 1))) ∨ ((x58 ≤ x38) ∧ (x38 ≤ x35) ∧ ((x35 - x58) ≥ 1) ∧ ((x35 - x38) ≤ (t - 1)) ∧ ((x38 - x58) ≤ (t - 1))))) : (((x58 - x38) ≤ (t - 1)) ∨ ((x38 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x38) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5585 (t x04 x36 x46 x47 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((t + x36 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x67)) ≥ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x36 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th322 t x04 x36 x46 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u3 (And.intro u2 u5))))))) h

theorem clause5586 (t x04 x07 x47 : ℝ) : (((x04 + ((-1) * x07)) ≤ 0) ∨ ((x07 + ((-1) * x47)) ≥ 0) ∨ (¬ (x04 ≤ x07)) ∨ (¬ (x07 ≤ x47)) ∨ (¬ ((x47 - x04) ≥ 1)) ∨ (¬ ((x07 - x04) ≤ (t - 1))) ∨ (¬ ((x47 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x07)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x47)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th324 t x04 x07 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5588 (t x04 x07 x47 : ℝ) : (((x04 + ((-1) * x47)) ≥ 1) ∨ ((x04 + ((-1) * x07)) ≤ 0) ∨ (¬ (x04 ≤ x07)) ∨ (¬ (x07 ≤ x47)) ∨ (¬ ((x47 - x04) ≥ 1)) ∨ (¬ ((x07 - x04) ≤ (t - 1))) ∨ (¬ ((x47 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x07)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th324 t x04 x07 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5593 (t x04 x07 x47 : ℝ) : (((x04 + ((-1) * x47)) ≥ 1) ∨ ((x07 + ((-1) * x47)) ≤ 0) ∨ (¬ (x04 ≤ x07)) ∨ (¬ (x07 ≤ x47)) ∨ (¬ ((x47 - x04) ≥ 1)) ∨ (¬ ((x07 - x04) ≤ (t - 1))) ∨ (¬ ((x47 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th324 t x04 x07 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5596 (t x04 x07 x47 : ℝ) : (((x04 + ((-1) * x47)) ≤ (-1)) ∨ ((x07 + ((-1) * x47)) ≥ 0) ∨ (¬ (x04 ≤ x07)) ∨ (¬ (x07 ≤ x47)) ∨ (¬ ((x47 - x04) ≥ 1)) ∨ (¬ ((x07 - x04) ≤ (t - 1))) ∨ (¬ ((x47 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x47)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th324 t x04 x07 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5597 (t x04 x07 x47 : ℝ) : (((x04 + ((-1) * x07)) ≥ 0) ∨ ((x04 + ((-1) * x47)) ≤ (-1)) ∨ (¬ (x04 ≤ x07)) ∨ (¬ (x07 ≤ x47)) ∨ (¬ ((x47 - x04) ≥ 1)) ∨ (¬ ((x07 - x04) ≤ (t - 1))) ∨ (¬ ((x47 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x07)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th324 t x04 x07 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5598 (t x04 x07 x47 : ℝ) : (((x04 + ((-1) * x47)) ≥ 1) ∨ ((x04 + ((-1) * x47)) ≤ (-1)) ∨ (¬ (x04 ≤ x07)) ∨ (¬ (x07 ≤ x47)) ∨ (¬ ((x47 - x04) ≥ 1)) ∨ (¬ ((x07 - x04) ≤ (t - 1))) ∨ (¬ ((x47 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th324 t x04 x07 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5611 (t x04 x07 x47 : ℝ) : (((x04 + ((-1) * x07)) ≤ 0) ∨ ((x07 + ((-1) * x47)) ≥ 0) ∨ (¬ (x47 ≤ x07)) ∨ (¬ (x07 ≤ x04)) ∨ (¬ ((x04 - x47) ≥ 1)) ∨ (¬ ((x04 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x07)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x47)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th324 t x04 x07 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5613 (t x04 x07 x47 : ℝ) : (((x04 + ((-1) * x47)) ≥ 1) ∨ ((x04 + ((-1) * x07)) ≤ 0) ∨ (¬ (x47 ≤ x07)) ∨ (¬ (x07 ≤ x04)) ∨ (¬ ((x04 - x47) ≥ 1)) ∨ (¬ ((x04 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x07)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th324 t x04 x07 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5617 (t x04 x07 x47 : ℝ) : (((x04 + ((-1) * x07)) ≥ 0) ∨ ((x07 + ((-1) * x47)) ≤ 0) ∨ (¬ (x47 ≤ x07)) ∨ (¬ (x07 ≤ x04)) ∨ (¬ ((x04 - x47) ≥ 1)) ∨ (¬ ((x04 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x07)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th324 t x04 x07 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5618 (t x04 x07 x47 : ℝ) : (((x04 + ((-1) * x47)) ≥ 1) ∨ ((x07 + ((-1) * x47)) ≤ 0) ∨ (¬ (x47 ≤ x07)) ∨ (¬ (x07 ≤ x04)) ∨ (¬ ((x04 - x47) ≥ 1)) ∨ (¬ ((x04 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th324 t x04 x07 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5621 (t x04 x07 x47 : ℝ) : (((x04 + ((-1) * x47)) ≤ (-1)) ∨ ((x07 + ((-1) * x47)) ≥ 0) ∨ (¬ (x47 ≤ x07)) ∨ (¬ (x07 ≤ x04)) ∨ (¬ ((x04 - x47) ≥ 1)) ∨ (¬ ((x04 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x47)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th324 t x04 x07 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5622 (t x04 x07 x47 : ℝ) : (((x04 + ((-1) * x07)) ≥ 0) ∨ ((x04 + ((-1) * x47)) ≤ (-1)) ∨ (¬ (x47 ≤ x07)) ∨ (¬ (x07 ≤ x04)) ∨ (¬ ((x04 - x47) ≥ 1)) ∨ (¬ ((x04 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x07)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th324 t x04 x07 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5623 (t x04 x07 x47 : ℝ) : (((x04 + ((-1) * x47)) ≥ 1) ∨ ((x04 + ((-1) * x47)) ≤ (-1)) ∨ (¬ (x47 ≤ x07)) ∨ (¬ (x07 ≤ x04)) ∨ (¬ ((x04 - x47) ≥ 1)) ∨ (¬ ((x04 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th324 t x04 x07 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5686 (t x04 x07 x47 : ℝ) (h : (((x04 ≤ x07) ∧ (x07 ≤ x47) ∧ ((x47 - x04) ≥ 1) ∧ ((x07 - x04) ≤ (t - 1)) ∧ ((x47 - x07) ≤ (t - 1))) ∨ ((x47 ≤ x07) ∧ (x07 ≤ x04) ∧ ((x04 - x47) ≥ 1) ∧ ((x04 - x07) ≤ (t - 1)) ∧ ((x07 - x47) ≤ (t - 1))))) : ((x04 ≤ x07) ∨ (x47 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5687 (t x04 x07 x47 : ℝ) (h : (((x04 ≤ x07) ∧ (x07 ≤ x47) ∧ ((x47 - x04) ≥ 1) ∧ ((x07 - x04) ≤ (t - 1)) ∧ ((x47 - x07) ≤ (t - 1))) ∨ ((x47 ≤ x07) ∧ (x07 ≤ x04) ∧ ((x04 - x47) ≥ 1) ∧ ((x04 - x07) ≤ (t - 1)) ∧ ((x07 - x47) ≤ (t - 1))))) : ((x04 ≤ x07) ∨ (x07 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5688 (t x04 x07 x47 : ℝ) (h : (((x04 ≤ x07) ∧ (x07 ≤ x47) ∧ ((x47 - x04) ≥ 1) ∧ ((x07 - x04) ≤ (t - 1)) ∧ ((x47 - x07) ≤ (t - 1))) ∨ ((x47 ≤ x07) ∧ (x07 ≤ x04) ∧ ((x04 - x47) ≥ 1) ∧ ((x04 - x07) ≤ (t - 1)) ∧ ((x07 - x47) ≤ (t - 1))))) : ((x04 ≤ x07) ∨ ((x04 - x47) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x47) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5689 (t x04 x07 x47 : ℝ) (h : (((x04 ≤ x07) ∧ (x07 ≤ x47) ∧ ((x47 - x04) ≥ 1) ∧ ((x07 - x04) ≤ (t - 1)) ∧ ((x47 - x07) ≤ (t - 1))) ∨ ((x47 ≤ x07) ∧ (x07 ≤ x04) ∧ ((x04 - x47) ≥ 1) ∧ ((x04 - x07) ≤ (t - 1)) ∧ ((x07 - x47) ≤ (t - 1))))) : ((x04 ≤ x07) ∨ ((x04 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5690 (t x04 x07 x47 : ℝ) (h : (((x04 ≤ x07) ∧ (x07 ≤ x47) ∧ ((x47 - x04) ≥ 1) ∧ ((x07 - x04) ≤ (t - 1)) ∧ ((x47 - x07) ≤ (t - 1))) ∨ ((x47 ≤ x07) ∧ (x07 ≤ x04) ∧ ((x04 - x47) ≥ 1) ∧ ((x04 - x07) ≤ (t - 1)) ∧ ((x07 - x47) ≤ (t - 1))))) : ((x04 ≤ x07) ∨ ((x07 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5691 (t x04 x07 x47 : ℝ) (h : (((x04 ≤ x07) ∧ (x07 ≤ x47) ∧ ((x47 - x04) ≥ 1) ∧ ((x07 - x04) ≤ (t - 1)) ∧ ((x47 - x07) ≤ (t - 1))) ∨ ((x47 ≤ x07) ∧ (x07 ≤ x04) ∧ ((x04 - x47) ≥ 1) ∧ ((x04 - x07) ≤ (t - 1)) ∧ ((x07 - x47) ≤ (t - 1))))) : ((x07 ≤ x47) ∨ (x47 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5692 (t x04 x07 x47 : ℝ) (h : (((x04 ≤ x07) ∧ (x07 ≤ x47) ∧ ((x47 - x04) ≥ 1) ∧ ((x07 - x04) ≤ (t - 1)) ∧ ((x47 - x07) ≤ (t - 1))) ∨ ((x47 ≤ x07) ∧ (x07 ≤ x04) ∧ ((x04 - x47) ≥ 1) ∧ ((x04 - x07) ≤ (t - 1)) ∧ ((x07 - x47) ≤ (t - 1))))) : ((x07 ≤ x47) ∨ (x07 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5693 (t x04 x07 x47 : ℝ) (h : (((x04 ≤ x07) ∧ (x07 ≤ x47) ∧ ((x47 - x04) ≥ 1) ∧ ((x07 - x04) ≤ (t - 1)) ∧ ((x47 - x07) ≤ (t - 1))) ∨ ((x47 ≤ x07) ∧ (x07 ≤ x04) ∧ ((x04 - x47) ≥ 1) ∧ ((x04 - x07) ≤ (t - 1)) ∧ ((x07 - x47) ≤ (t - 1))))) : ((x07 ≤ x47) ∨ ((x04 - x47) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x47) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5694 (t x04 x07 x47 : ℝ) (h : (((x04 ≤ x07) ∧ (x07 ≤ x47) ∧ ((x47 - x04) ≥ 1) ∧ ((x07 - x04) ≤ (t - 1)) ∧ ((x47 - x07) ≤ (t - 1))) ∨ ((x47 ≤ x07) ∧ (x07 ≤ x04) ∧ ((x04 - x47) ≥ 1) ∧ ((x04 - x07) ≤ (t - 1)) ∧ ((x07 - x47) ≤ (t - 1))))) : ((x07 ≤ x47) ∨ ((x04 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5695 (t x04 x07 x47 : ℝ) (h : (((x04 ≤ x07) ∧ (x07 ≤ x47) ∧ ((x47 - x04) ≥ 1) ∧ ((x07 - x04) ≤ (t - 1)) ∧ ((x47 - x07) ≤ (t - 1))) ∨ ((x47 ≤ x07) ∧ (x07 ≤ x04) ∧ ((x04 - x47) ≥ 1) ∧ ((x04 - x07) ≤ (t - 1)) ∧ ((x07 - x47) ≤ (t - 1))))) : ((x07 ≤ x47) ∨ ((x07 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5696 (t x04 x07 x47 : ℝ) (h : (((x04 ≤ x07) ∧ (x07 ≤ x47) ∧ ((x47 - x04) ≥ 1) ∧ ((x07 - x04) ≤ (t - 1)) ∧ ((x47 - x07) ≤ (t - 1))) ∨ ((x47 ≤ x07) ∧ (x07 ≤ x04) ∧ ((x04 - x47) ≥ 1) ∧ ((x04 - x07) ≤ (t - 1)) ∧ ((x07 - x47) ≤ (t - 1))))) : (((x47 - x04) ≥ 1) ∨ (x47 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x04) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5697 (t x04 x07 x47 : ℝ) (h : (((x04 ≤ x07) ∧ (x07 ≤ x47) ∧ ((x47 - x04) ≥ 1) ∧ ((x07 - x04) ≤ (t - 1)) ∧ ((x47 - x07) ≤ (t - 1))) ∨ ((x47 ≤ x07) ∧ (x07 ≤ x04) ∧ ((x04 - x47) ≥ 1) ∧ ((x04 - x07) ≤ (t - 1)) ∧ ((x07 - x47) ≤ (t - 1))))) : (((x47 - x04) ≥ 1) ∨ (x07 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x04) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5698 (t x04 x07 x47 : ℝ) (h : (((x04 ≤ x07) ∧ (x07 ≤ x47) ∧ ((x47 - x04) ≥ 1) ∧ ((x07 - x04) ≤ (t - 1)) ∧ ((x47 - x07) ≤ (t - 1))) ∨ ((x47 ≤ x07) ∧ (x07 ≤ x04) ∧ ((x04 - x47) ≥ 1) ∧ ((x04 - x07) ≤ (t - 1)) ∧ ((x07 - x47) ≤ (t - 1))))) : (((x47 - x04) ≥ 1) ∨ ((x04 - x47) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x04) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x47) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5699 (t x04 x07 x47 : ℝ) (h : (((x04 ≤ x07) ∧ (x07 ≤ x47) ∧ ((x47 - x04) ≥ 1) ∧ ((x07 - x04) ≤ (t - 1)) ∧ ((x47 - x07) ≤ (t - 1))) ∨ ((x47 ≤ x07) ∧ (x07 ≤ x04) ∧ ((x04 - x47) ≥ 1) ∧ ((x04 - x07) ≤ (t - 1)) ∧ ((x07 - x47) ≤ (t - 1))))) : (((x47 - x04) ≥ 1) ∨ ((x04 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x04) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5700 (t x04 x07 x47 : ℝ) (h : (((x04 ≤ x07) ∧ (x07 ≤ x47) ∧ ((x47 - x04) ≥ 1) ∧ ((x07 - x04) ≤ (t - 1)) ∧ ((x47 - x07) ≤ (t - 1))) ∨ ((x47 ≤ x07) ∧ (x07 ≤ x04) ∧ ((x04 - x47) ≥ 1) ∧ ((x04 - x07) ≤ (t - 1)) ∧ ((x07 - x47) ≤ (t - 1))))) : (((x47 - x04) ≥ 1) ∨ ((x07 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x04) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5701 (t x04 x07 x47 : ℝ) (h : (((x04 ≤ x07) ∧ (x07 ≤ x47) ∧ ((x47 - x04) ≥ 1) ∧ ((x07 - x04) ≤ (t - 1)) ∧ ((x47 - x07) ≤ (t - 1))) ∨ ((x47 ≤ x07) ∧ (x07 ≤ x04) ∧ ((x04 - x47) ≥ 1) ∧ ((x04 - x07) ≤ (t - 1)) ∧ ((x07 - x47) ≤ (t - 1))))) : (((x07 - x04) ≤ (t - 1)) ∨ (x47 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5702 (t x04 x07 x47 : ℝ) (h : (((x04 ≤ x07) ∧ (x07 ≤ x47) ∧ ((x47 - x04) ≥ 1) ∧ ((x07 - x04) ≤ (t - 1)) ∧ ((x47 - x07) ≤ (t - 1))) ∨ ((x47 ≤ x07) ∧ (x07 ≤ x04) ∧ ((x04 - x47) ≥ 1) ∧ ((x04 - x07) ≤ (t - 1)) ∧ ((x07 - x47) ≤ (t - 1))))) : (((x07 - x04) ≤ (t - 1)) ∨ (x07 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5703 (t x04 x07 x47 : ℝ) (h : (((x04 ≤ x07) ∧ (x07 ≤ x47) ∧ ((x47 - x04) ≥ 1) ∧ ((x07 - x04) ≤ (t - 1)) ∧ ((x47 - x07) ≤ (t - 1))) ∨ ((x47 ≤ x07) ∧ (x07 ≤ x04) ∧ ((x04 - x47) ≥ 1) ∧ ((x04 - x07) ≤ (t - 1)) ∧ ((x07 - x47) ≤ (t - 1))))) : (((x07 - x04) ≤ (t - 1)) ∨ ((x04 - x47) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x47) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5704 (t x04 x07 x47 : ℝ) (h : (((x04 ≤ x07) ∧ (x07 ≤ x47) ∧ ((x47 - x04) ≥ 1) ∧ ((x07 - x04) ≤ (t - 1)) ∧ ((x47 - x07) ≤ (t - 1))) ∨ ((x47 ≤ x07) ∧ (x07 ≤ x04) ∧ ((x04 - x47) ≥ 1) ∧ ((x04 - x07) ≤ (t - 1)) ∧ ((x07 - x47) ≤ (t - 1))))) : (((x07 - x04) ≤ (t - 1)) ∨ ((x04 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5705 (t x04 x07 x47 : ℝ) (h : (((x04 ≤ x07) ∧ (x07 ≤ x47) ∧ ((x47 - x04) ≥ 1) ∧ ((x07 - x04) ≤ (t - 1)) ∧ ((x47 - x07) ≤ (t - 1))) ∨ ((x47 ≤ x07) ∧ (x07 ≤ x04) ∧ ((x04 - x47) ≥ 1) ∧ ((x04 - x07) ≤ (t - 1)) ∧ ((x07 - x47) ≤ (t - 1))))) : (((x07 - x04) ≤ (t - 1)) ∨ ((x07 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5706 (t x04 x07 x47 : ℝ) (h : (((x04 ≤ x07) ∧ (x07 ≤ x47) ∧ ((x47 - x04) ≥ 1) ∧ ((x07 - x04) ≤ (t - 1)) ∧ ((x47 - x07) ≤ (t - 1))) ∨ ((x47 ≤ x07) ∧ (x07 ≤ x04) ∧ ((x04 - x47) ≥ 1) ∧ ((x04 - x07) ≤ (t - 1)) ∧ ((x07 - x47) ≤ (t - 1))))) : (((x47 - x07) ≤ (t - 1)) ∨ (x47 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5707 (t x04 x07 x47 : ℝ) (h : (((x04 ≤ x07) ∧ (x07 ≤ x47) ∧ ((x47 - x04) ≥ 1) ∧ ((x07 - x04) ≤ (t - 1)) ∧ ((x47 - x07) ≤ (t - 1))) ∨ ((x47 ≤ x07) ∧ (x07 ≤ x04) ∧ ((x04 - x47) ≥ 1) ∧ ((x04 - x07) ≤ (t - 1)) ∧ ((x07 - x47) ≤ (t - 1))))) : (((x47 - x07) ≤ (t - 1)) ∨ (x07 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5708 (t x04 x07 x47 : ℝ) (h : (((x04 ≤ x07) ∧ (x07 ≤ x47) ∧ ((x47 - x04) ≥ 1) ∧ ((x07 - x04) ≤ (t - 1)) ∧ ((x47 - x07) ≤ (t - 1))) ∨ ((x47 ≤ x07) ∧ (x07 ≤ x04) ∧ ((x04 - x47) ≥ 1) ∧ ((x04 - x07) ≤ (t - 1)) ∧ ((x07 - x47) ≤ (t - 1))))) : (((x47 - x07) ≤ (t - 1)) ∨ ((x04 - x47) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x47) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5709 (t x04 x07 x47 : ℝ) (h : (((x04 ≤ x07) ∧ (x07 ≤ x47) ∧ ((x47 - x04) ≥ 1) ∧ ((x07 - x04) ≤ (t - 1)) ∧ ((x47 - x07) ≤ (t - 1))) ∨ ((x47 ≤ x07) ∧ (x07 ≤ x04) ∧ ((x04 - x47) ≥ 1) ∧ ((x04 - x07) ≤ (t - 1)) ∧ ((x07 - x47) ≤ (t - 1))))) : (((x47 - x07) ≤ (t - 1)) ∨ ((x04 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5710 (t x04 x07 x47 : ℝ) (h : (((x04 ≤ x07) ∧ (x07 ≤ x47) ∧ ((x47 - x04) ≥ 1) ∧ ((x07 - x04) ≤ (t - 1)) ∧ ((x47 - x07) ≤ (t - 1))) ∨ ((x47 ≤ x07) ∧ (x07 ≤ x04) ∧ ((x04 - x47) ≥ 1) ∧ ((x04 - x07) ≤ (t - 1)) ∧ ((x07 - x47) ≤ (t - 1))))) : (((x47 - x07) ≤ (t - 1)) ∨ ((x07 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5711 (t x01 x04 x06 x14 x36 x46 x47 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x36 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((t + x01 + ((-1) * x06)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x36 + ((-1) * x46)) ≥ 1) := by
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
  have u4 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x47)) ≥ 1) := by
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
  have u8 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th326 t x01 x04 x06 x14 x36 x46 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u7 (And.intro u4 (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u6 (And.intro u5 u8)))))))))) h

theorem clause5714 (t x57 x58 x78 : ℝ) : (((x57 + ((-1) * x58)) ≤ 0) ∨ ((x57 + ((-1) * x78)) ≥ 1) ∨ (¬ (x57 ≤ x58)) ∨ (¬ (x58 ≤ x78)) ∨ (¬ ((x78 - x57) ≥ 1)) ∨ (¬ ((x58 - x57) ≤ (t - 1))) ∨ (¬ ((x78 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 + ((-1) * x58)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x58 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th329 t x57 x58 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5716 (t x57 x58 x78 : ℝ) : (((x57 + ((-1) * x58)) ≤ 0) ∨ ((t + ((-1) * x58) + x78) ≥ 1) ∨ (¬ (x57 ≤ x58)) ∨ (¬ (x58 ≤ x78)) ∨ (¬ ((x78 - x57) ≥ 1)) ∨ (¬ ((x58 - x57) ≤ (t - 1))) ∨ (¬ ((x78 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 + ((-1) * x58)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x58) + x78) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x58 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th329 t x57 x58 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5719 (t x57 x58 x78 : ℝ) : (((x58 + ((-1) * x78)) ≤ 0) ∨ ((x57 + ((-1) * x78)) ≥ 1) ∨ (¬ (x57 ≤ x58)) ∨ (¬ (x58 ≤ x78)) ∨ (¬ ((x78 - x57) ≥ 1)) ∨ (¬ ((x58 - x57) ≤ (t - 1))) ∨ (¬ ((x78 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x58 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th329 t x57 x58 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5721 (t x57 x58 x78 : ℝ) : (((x58 + ((-1) * x78)) ≤ 0) ∨ ((t + ((-1) * x58) + x78) ≥ 1) ∨ (¬ (x57 ≤ x58)) ∨ (¬ (x58 ≤ x78)) ∨ (¬ ((x78 - x57) ≥ 1)) ∨ (¬ ((x58 - x57) ≤ (t - 1))) ∨ (¬ ((x78 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x58) + x78) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x58 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th329 t x57 x58 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5723 (t x57 x58 x78 : ℝ) : (((x57 + ((-1) * x78)) ≤ (-1)) ∨ ((x57 + ((-1) * x58)) ≥ 0) ∨ (¬ (x57 ≤ x58)) ∨ (¬ (x58 ≤ x78)) ∨ (¬ ((x78 - x57) ≥ 1)) ∨ (¬ ((x58 - x57) ≤ (t - 1))) ∨ (¬ ((x78 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 + ((-1) * x58)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x58 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th329 t x57 x58 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5724 (t x57 x58 x78 : ℝ) : (((x57 + ((-1) * x78)) ≤ (-1)) ∨ ((x57 + ((-1) * x78)) ≥ 1) ∨ (¬ (x57 ≤ x58)) ∨ (¬ (x58 ≤ x78)) ∨ (¬ ((x78 - x57) ≥ 1)) ∨ (¬ ((x58 - x57) ≤ (t - 1))) ∨ (¬ ((x78 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x58 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th329 t x57 x58 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5726 (t x57 x58 x78 : ℝ) : (((x57 + ((-1) * x78)) ≤ (-1)) ∨ ((t + ((-1) * x58) + x78) ≥ 1) ∨ (¬ (x57 ≤ x58)) ∨ (¬ (x58 ≤ x78)) ∨ (¬ ((x78 - x57) ≥ 1)) ∨ (¬ ((x58 - x57) ≤ (t - 1))) ∨ (¬ ((x78 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x58) + x78) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x58 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th329 t x57 x58 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5729 (t x57 x58 x78 : ℝ) : (((t + x57 + ((-1) * x58)) ≥ 1) ∨ ((x57 + ((-1) * x78)) ≥ 1) ∨ (¬ (x57 ≤ x58)) ∨ (¬ (x58 ≤ x78)) ∨ (¬ ((x78 - x57) ≥ 1)) ∨ (¬ ((x58 - x57) ≤ (t - 1))) ∨ (¬ ((x78 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x57 + ((-1) * x58)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x58 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th329 t x57 x58 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5734 (t x57 x58 x78 : ℝ) : (((t + x58 + ((-1) * x78)) ≥ 1) ∨ ((x57 + ((-1) * x78)) ≥ 1) ∨ (¬ (x57 ≤ x58)) ∨ (¬ (x58 ≤ x78)) ∨ (¬ ((x78 - x57) ≥ 1)) ∨ (¬ ((x58 - x57) ≤ (t - 1))) ∨ (¬ ((x78 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x58 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x58 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th329 t x57 x58 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5739 (t x57 x58 x78 : ℝ) : (((x57 + ((-1) * x58)) ≤ 0) ∨ ((x57 + ((-1) * x78)) ≥ 1) ∨ (¬ (x78 ≤ x58)) ∨ (¬ (x58 ≤ x57)) ∨ (¬ ((x57 - x78) ≥ 1)) ∨ (¬ ((x57 - x58) ≤ (t - 1))) ∨ (¬ ((x58 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 + ((-1) * x58)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th329 t x57 x58 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5741 (t x57 x58 x78 : ℝ) : (((x57 + ((-1) * x58)) ≤ 0) ∨ ((t + ((-1) * x58) + x78) ≥ 1) ∨ (¬ (x78 ≤ x58)) ∨ (¬ (x58 ≤ x57)) ∨ (¬ ((x57 - x78) ≥ 1)) ∨ (¬ ((x57 - x58) ≤ (t - 1))) ∨ (¬ ((x58 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 + ((-1) * x58)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x58) + x78) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th329 t x57 x58 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5744 (t x57 x58 x78 : ℝ) : (((x58 + ((-1) * x78)) ≤ 0) ∨ ((x57 + ((-1) * x78)) ≥ 1) ∨ (¬ (x78 ≤ x58)) ∨ (¬ (x58 ≤ x57)) ∨ (¬ ((x57 - x78) ≥ 1)) ∨ (¬ ((x57 - x58) ≤ (t - 1))) ∨ (¬ ((x58 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th329 t x57 x58 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5748 (t x57 x58 x78 : ℝ) : (((x57 + ((-1) * x78)) ≤ (-1)) ∨ ((x57 + ((-1) * x58)) ≥ 0) ∨ (¬ (x78 ≤ x58)) ∨ (¬ (x58 ≤ x57)) ∨ (¬ ((x57 - x78) ≥ 1)) ∨ (¬ ((x57 - x58) ≤ (t - 1))) ∨ (¬ ((x58 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 + ((-1) * x58)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th329 t x57 x58 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5749 (t x57 x58 x78 : ℝ) : (((x57 + ((-1) * x78)) ≤ (-1)) ∨ ((x57 + ((-1) * x78)) ≥ 1) ∨ (¬ (x78 ≤ x58)) ∨ (¬ (x58 ≤ x57)) ∨ (¬ ((x57 - x78) ≥ 1)) ∨ (¬ ((x57 - x58) ≤ (t - 1))) ∨ (¬ ((x58 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th329 t x57 x58 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5751 (t x57 x58 x78 : ℝ) : (((x57 + ((-1) * x78)) ≤ (-1)) ∨ ((t + ((-1) * x58) + x78) ≥ 1) ∨ (¬ (x78 ≤ x58)) ∨ (¬ (x58 ≤ x57)) ∨ (¬ ((x57 - x78) ≥ 1)) ∨ (¬ ((x57 - x58) ≤ (t - 1))) ∨ (¬ ((x58 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x58) + x78) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th329 t x57 x58 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5753 (t x57 x58 x78 : ℝ) : (((t + x57 + ((-1) * x58)) ≥ 1) ∨ ((x57 + ((-1) * x58)) ≥ 0) ∨ (¬ (x78 ≤ x58)) ∨ (¬ (x58 ≤ x57)) ∨ (¬ ((x57 - x78) ≥ 1)) ∨ (¬ ((x57 - x58) ≤ (t - 1))) ∨ (¬ ((x58 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x57 + ((-1) * x58)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 + ((-1) * x58)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th329 t x57 x58 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5759 (t x57 x58 x78 : ℝ) : (((t + x58 + ((-1) * x78)) ≥ 1) ∨ ((x57 + ((-1) * x78)) ≥ 1) ∨ (¬ (x78 ≤ x58)) ∨ (¬ (x58 ≤ x57)) ∨ (¬ ((x57 - x78) ≥ 1)) ∨ (¬ ((x57 - x58) ≤ (t - 1))) ∨ (¬ ((x58 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x58 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th329 t x57 x58 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5812 (t x57 x58 x78 : ℝ) (h : (((x57 ≤ x58) ∧ (x58 ≤ x78) ∧ ((x78 - x57) ≥ 1) ∧ ((x58 - x57) ≤ (t - 1)) ∧ ((x78 - x58) ≤ (t - 1))) ∨ ((x78 ≤ x58) ∧ (x58 ≤ x57) ∧ ((x57 - x78) ≥ 1) ∧ ((x57 - x58) ≤ (t - 1)) ∧ ((x58 - x78) ≤ (t - 1))))) : ((x57 ≤ x58) ∨ (x78 ≤ x58)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x57 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x58) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5813 (t x57 x58 x78 : ℝ) (h : (((x57 ≤ x58) ∧ (x58 ≤ x78) ∧ ((x78 - x57) ≥ 1) ∧ ((x58 - x57) ≤ (t - 1)) ∧ ((x78 - x58) ≤ (t - 1))) ∨ ((x78 ≤ x58) ∧ (x58 ≤ x57) ∧ ((x57 - x78) ≥ 1) ∧ ((x57 - x58) ≤ (t - 1)) ∧ ((x58 - x78) ≤ (t - 1))))) : ((x57 ≤ x58) ∨ (x58 ≤ x57)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x57 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x57) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5814 (t x57 x58 x78 : ℝ) (h : (((x57 ≤ x58) ∧ (x58 ≤ x78) ∧ ((x78 - x57) ≥ 1) ∧ ((x58 - x57) ≤ (t - 1)) ∧ ((x78 - x58) ≤ (t - 1))) ∨ ((x78 ≤ x58) ∧ (x58 ≤ x57) ∧ ((x57 - x78) ≥ 1) ∧ ((x57 - x58) ≤ (t - 1)) ∧ ((x58 - x78) ≤ (t - 1))))) : ((x57 ≤ x58) ∨ ((x57 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x57 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5815 (t x57 x58 x78 : ℝ) (h : (((x57 ≤ x58) ∧ (x58 ≤ x78) ∧ ((x78 - x57) ≥ 1) ∧ ((x58 - x57) ≤ (t - 1)) ∧ ((x78 - x58) ≤ (t - 1))) ∨ ((x78 ≤ x58) ∧ (x58 ≤ x57) ∧ ((x57 - x78) ≥ 1) ∧ ((x57 - x58) ≤ (t - 1)) ∧ ((x58 - x78) ≤ (t - 1))))) : ((x57 ≤ x58) ∨ ((x57 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x57 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5816 (t x57 x58 x78 : ℝ) (h : (((x57 ≤ x58) ∧ (x58 ≤ x78) ∧ ((x78 - x57) ≥ 1) ∧ ((x58 - x57) ≤ (t - 1)) ∧ ((x78 - x58) ≤ (t - 1))) ∨ ((x78 ≤ x58) ∧ (x58 ≤ x57) ∧ ((x57 - x78) ≥ 1) ∧ ((x57 - x58) ≤ (t - 1)) ∧ ((x58 - x78) ≤ (t - 1))))) : ((x57 ≤ x58) ∨ ((x58 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x57 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x58 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5817 (t x57 x58 x78 : ℝ) (h : (((x57 ≤ x58) ∧ (x58 ≤ x78) ∧ ((x78 - x57) ≥ 1) ∧ ((x58 - x57) ≤ (t - 1)) ∧ ((x78 - x58) ≤ (t - 1))) ∨ ((x78 ≤ x58) ∧ (x58 ≤ x57) ∧ ((x57 - x78) ≥ 1) ∧ ((x57 - x58) ≤ (t - 1)) ∧ ((x58 - x78) ≤ (t - 1))))) : ((x58 ≤ x78) ∨ (x78 ≤ x58)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x58 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x58) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5818 (t x57 x58 x78 : ℝ) (h : (((x57 ≤ x58) ∧ (x58 ≤ x78) ∧ ((x78 - x57) ≥ 1) ∧ ((x58 - x57) ≤ (t - 1)) ∧ ((x78 - x58) ≤ (t - 1))) ∨ ((x78 ≤ x58) ∧ (x58 ≤ x57) ∧ ((x57 - x78) ≥ 1) ∧ ((x57 - x58) ≤ (t - 1)) ∧ ((x58 - x78) ≤ (t - 1))))) : ((x58 ≤ x78) ∨ (x58 ≤ x57)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x58 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x57) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5819 (t x57 x58 x78 : ℝ) (h : (((x57 ≤ x58) ∧ (x58 ≤ x78) ∧ ((x78 - x57) ≥ 1) ∧ ((x58 - x57) ≤ (t - 1)) ∧ ((x78 - x58) ≤ (t - 1))) ∨ ((x78 ≤ x58) ∧ (x58 ≤ x57) ∧ ((x57 - x78) ≥ 1) ∧ ((x57 - x58) ≤ (t - 1)) ∧ ((x58 - x78) ≤ (t - 1))))) : ((x58 ≤ x78) ∨ ((x57 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x58 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5820 (t x57 x58 x78 : ℝ) (h : (((x57 ≤ x58) ∧ (x58 ≤ x78) ∧ ((x78 - x57) ≥ 1) ∧ ((x58 - x57) ≤ (t - 1)) ∧ ((x78 - x58) ≤ (t - 1))) ∨ ((x78 ≤ x58) ∧ (x58 ≤ x57) ∧ ((x57 - x78) ≥ 1) ∧ ((x57 - x58) ≤ (t - 1)) ∧ ((x58 - x78) ≤ (t - 1))))) : ((x58 ≤ x78) ∨ ((x57 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x58 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5821 (t x57 x58 x78 : ℝ) (h : (((x57 ≤ x58) ∧ (x58 ≤ x78) ∧ ((x78 - x57) ≥ 1) ∧ ((x58 - x57) ≤ (t - 1)) ∧ ((x78 - x58) ≤ (t - 1))) ∨ ((x78 ≤ x58) ∧ (x58 ≤ x57) ∧ ((x57 - x78) ≥ 1) ∧ ((x57 - x58) ≤ (t - 1)) ∧ ((x58 - x78) ≤ (t - 1))))) : ((x58 ≤ x78) ∨ ((x58 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x58 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x58 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5822 (t x57 x58 x78 : ℝ) (h : (((x57 ≤ x58) ∧ (x58 ≤ x78) ∧ ((x78 - x57) ≥ 1) ∧ ((x58 - x57) ≤ (t - 1)) ∧ ((x78 - x58) ≤ (t - 1))) ∨ ((x78 ≤ x58) ∧ (x58 ≤ x57) ∧ ((x57 - x78) ≥ 1) ∧ ((x57 - x58) ≤ (t - 1)) ∧ ((x58 - x78) ≤ (t - 1))))) : (((x78 - x57) ≥ 1) ∨ (x78 ≤ x58)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x57) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x58) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5823 (t x57 x58 x78 : ℝ) (h : (((x57 ≤ x58) ∧ (x58 ≤ x78) ∧ ((x78 - x57) ≥ 1) ∧ ((x58 - x57) ≤ (t - 1)) ∧ ((x78 - x58) ≤ (t - 1))) ∨ ((x78 ≤ x58) ∧ (x58 ≤ x57) ∧ ((x57 - x78) ≥ 1) ∧ ((x57 - x58) ≤ (t - 1)) ∧ ((x58 - x78) ≤ (t - 1))))) : (((x78 - x57) ≥ 1) ∨ (x58 ≤ x57)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x57) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x57) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5824 (t x57 x58 x78 : ℝ) (h : (((x57 ≤ x58) ∧ (x58 ≤ x78) ∧ ((x78 - x57) ≥ 1) ∧ ((x58 - x57) ≤ (t - 1)) ∧ ((x78 - x58) ≤ (t - 1))) ∨ ((x78 ≤ x58) ∧ (x58 ≤ x57) ∧ ((x57 - x78) ≥ 1) ∧ ((x57 - x58) ≤ (t - 1)) ∧ ((x58 - x78) ≤ (t - 1))))) : (((x78 - x57) ≥ 1) ∨ ((x57 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x57) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5825 (t x57 x58 x78 : ℝ) (h : (((x57 ≤ x58) ∧ (x58 ≤ x78) ∧ ((x78 - x57) ≥ 1) ∧ ((x58 - x57) ≤ (t - 1)) ∧ ((x78 - x58) ≤ (t - 1))) ∨ ((x78 ≤ x58) ∧ (x58 ≤ x57) ∧ ((x57 - x78) ≥ 1) ∧ ((x57 - x58) ≤ (t - 1)) ∧ ((x58 - x78) ≤ (t - 1))))) : (((x78 - x57) ≥ 1) ∨ ((x57 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x57) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5826 (t x57 x58 x78 : ℝ) (h : (((x57 ≤ x58) ∧ (x58 ≤ x78) ∧ ((x78 - x57) ≥ 1) ∧ ((x58 - x57) ≤ (t - 1)) ∧ ((x78 - x58) ≤ (t - 1))) ∨ ((x78 ≤ x58) ∧ (x58 ≤ x57) ∧ ((x57 - x78) ≥ 1) ∧ ((x57 - x58) ≤ (t - 1)) ∧ ((x58 - x78) ≤ (t - 1))))) : (((x78 - x57) ≥ 1) ∨ ((x58 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x57) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x58 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5827 (t x57 x58 x78 : ℝ) (h : (((x57 ≤ x58) ∧ (x58 ≤ x78) ∧ ((x78 - x57) ≥ 1) ∧ ((x58 - x57) ≤ (t - 1)) ∧ ((x78 - x58) ≤ (t - 1))) ∨ ((x78 ≤ x58) ∧ (x58 ≤ x57) ∧ ((x57 - x78) ≥ 1) ∧ ((x57 - x58) ≤ (t - 1)) ∧ ((x58 - x78) ≤ (t - 1))))) : (((x58 - x57) ≤ (t - 1)) ∨ (x78 ≤ x58)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x57) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x58) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5828 (t x57 x58 x78 : ℝ) (h : (((x57 ≤ x58) ∧ (x58 ≤ x78) ∧ ((x78 - x57) ≥ 1) ∧ ((x58 - x57) ≤ (t - 1)) ∧ ((x78 - x58) ≤ (t - 1))) ∨ ((x78 ≤ x58) ∧ (x58 ≤ x57) ∧ ((x57 - x78) ≥ 1) ∧ ((x57 - x58) ≤ (t - 1)) ∧ ((x58 - x78) ≤ (t - 1))))) : (((x58 - x57) ≤ (t - 1)) ∨ (x58 ≤ x57)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x57) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x57) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5829 (t x57 x58 x78 : ℝ) (h : (((x57 ≤ x58) ∧ (x58 ≤ x78) ∧ ((x78 - x57) ≥ 1) ∧ ((x58 - x57) ≤ (t - 1)) ∧ ((x78 - x58) ≤ (t - 1))) ∨ ((x78 ≤ x58) ∧ (x58 ≤ x57) ∧ ((x57 - x78) ≥ 1) ∧ ((x57 - x58) ≤ (t - 1)) ∧ ((x58 - x78) ≤ (t - 1))))) : (((x58 - x57) ≤ (t - 1)) ∨ ((x57 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x57) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5830 (t x57 x58 x78 : ℝ) (h : (((x57 ≤ x58) ∧ (x58 ≤ x78) ∧ ((x78 - x57) ≥ 1) ∧ ((x58 - x57) ≤ (t - 1)) ∧ ((x78 - x58) ≤ (t - 1))) ∨ ((x78 ≤ x58) ∧ (x58 ≤ x57) ∧ ((x57 - x78) ≥ 1) ∧ ((x57 - x58) ≤ (t - 1)) ∧ ((x58 - x78) ≤ (t - 1))))) : (((x58 - x57) ≤ (t - 1)) ∨ ((x57 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x57) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5831 (t x57 x58 x78 : ℝ) (h : (((x57 ≤ x58) ∧ (x58 ≤ x78) ∧ ((x78 - x57) ≥ 1) ∧ ((x58 - x57) ≤ (t - 1)) ∧ ((x78 - x58) ≤ (t - 1))) ∨ ((x78 ≤ x58) ∧ (x58 ≤ x57) ∧ ((x57 - x78) ≥ 1) ∧ ((x57 - x58) ≤ (t - 1)) ∧ ((x58 - x78) ≤ (t - 1))))) : (((x58 - x57) ≤ (t - 1)) ∨ ((x58 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x57) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x58 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5832 (t x57 x58 x78 : ℝ) (h : (((x57 ≤ x58) ∧ (x58 ≤ x78) ∧ ((x78 - x57) ≥ 1) ∧ ((x58 - x57) ≤ (t - 1)) ∧ ((x78 - x58) ≤ (t - 1))) ∨ ((x78 ≤ x58) ∧ (x58 ≤ x57) ∧ ((x57 - x78) ≥ 1) ∧ ((x57 - x58) ≤ (t - 1)) ∧ ((x58 - x78) ≤ (t - 1))))) : (((x78 - x58) ≤ (t - 1)) ∨ (x78 ≤ x58)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x58) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x58) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5833 (t x57 x58 x78 : ℝ) (h : (((x57 ≤ x58) ∧ (x58 ≤ x78) ∧ ((x78 - x57) ≥ 1) ∧ ((x58 - x57) ≤ (t - 1)) ∧ ((x78 - x58) ≤ (t - 1))) ∨ ((x78 ≤ x58) ∧ (x58 ≤ x57) ∧ ((x57 - x78) ≥ 1) ∧ ((x57 - x58) ≤ (t - 1)) ∧ ((x58 - x78) ≤ (t - 1))))) : (((x78 - x58) ≤ (t - 1)) ∨ (x58 ≤ x57)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x58) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x57) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5834 (t x57 x58 x78 : ℝ) (h : (((x57 ≤ x58) ∧ (x58 ≤ x78) ∧ ((x78 - x57) ≥ 1) ∧ ((x58 - x57) ≤ (t - 1)) ∧ ((x78 - x58) ≤ (t - 1))) ∨ ((x78 ≤ x58) ∧ (x58 ≤ x57) ∧ ((x57 - x78) ≥ 1) ∧ ((x57 - x58) ≤ (t - 1)) ∧ ((x58 - x78) ≤ (t - 1))))) : (((x78 - x58) ≤ (t - 1)) ∨ ((x57 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x58) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5835 (t x57 x58 x78 : ℝ) (h : (((x57 ≤ x58) ∧ (x58 ≤ x78) ∧ ((x78 - x57) ≥ 1) ∧ ((x58 - x57) ≤ (t - 1)) ∧ ((x78 - x58) ≤ (t - 1))) ∨ ((x78 ≤ x58) ∧ (x58 ≤ x57) ∧ ((x57 - x78) ≥ 1) ∧ ((x57 - x58) ≤ (t - 1)) ∧ ((x58 - x78) ≤ (t - 1))))) : (((x78 - x58) ≤ (t - 1)) ∨ ((x57 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x58) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5836 (t x57 x58 x78 : ℝ) (h : (((x57 ≤ x58) ∧ (x58 ≤ x78) ∧ ((x78 - x57) ≥ 1) ∧ ((x58 - x57) ≤ (t - 1)) ∧ ((x78 - x58) ≤ (t - 1))) ∨ ((x78 ≤ x58) ∧ (x58 ≤ x57) ∧ ((x57 - x78) ≥ 1) ∧ ((x57 - x58) ≤ (t - 1)) ∧ ((x58 - x78) ≤ (t - 1))))) : (((x78 - x58) ≤ (t - 1)) ∨ ((x58 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x58) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x58 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5837 (x36 x67 : ℝ) : ((¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th331 x36 x67
  exact (fun hh => (Or.elim hh (fun hh => hh u0) (fun zz => ((fun hh => hh u1) zz)))) h

theorem clause5838 (t x36 x37 x67 : ℝ) : (((x36 + ((-1) * x37)) ≤ 0) ∨ ((x37 + ((-1) * x67)) ≥ 0) ∨ (¬ (x36 ≤ x37)) ∨ (¬ (x37 ≤ x67)) ∨ (¬ ((x67 - x36) ≥ 1)) ∨ (¬ ((x37 - x36) ≤ (t - 1))) ∨ (¬ ((x67 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x37)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th333 t x36 x37 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5840 (t x36 x37 x67 : ℝ) : (((x36 + ((-1) * x67)) ≥ 1) ∨ ((x36 + ((-1) * x37)) ≤ 0) ∨ (¬ (x36 ≤ x37)) ∨ (¬ (x37 ≤ x67)) ∨ (¬ ((x67 - x36) ≥ 1)) ∨ (¬ ((x37 - x36) ≤ (t - 1))) ∨ (¬ ((x67 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 + ((-1) * x37)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th333 t x36 x37 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5844 (t x36 x37 x67 : ℝ) : (((x37 + ((-1) * x67)) ≤ 0) ∨ ((x36 + ((-1) * x37)) ≥ 0) ∨ (¬ (x36 ≤ x37)) ∨ (¬ (x37 ≤ x67)) ∨ (¬ ((x67 - x36) ≥ 1)) ∨ (¬ ((x37 - x36) ≤ (t - 1))) ∨ (¬ ((x67 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th333 t x36 x37 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5845 (t x36 x37 x67 : ℝ) : (((x36 + ((-1) * x67)) ≥ 1) ∨ ((x37 + ((-1) * x67)) ≤ 0) ∨ (¬ (x36 ≤ x37)) ∨ (¬ (x37 ≤ x67)) ∨ (¬ ((x67 - x36) ≥ 1)) ∨ (¬ ((x37 - x36) ≤ (t - 1))) ∨ (¬ ((x67 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th333 t x36 x37 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5848 (t x36 x37 x67 : ℝ) : (((x36 + ((-1) * x67)) ≤ (-1)) ∨ ((x37 + ((-1) * x67)) ≥ 0) ∨ (¬ (x36 ≤ x37)) ∨ (¬ (x37 ≤ x67)) ∨ (¬ ((x67 - x36) ≥ 1)) ∨ (¬ ((x37 - x36) ≤ (t - 1))) ∨ (¬ ((x67 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th333 t x36 x37 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5849 (t x36 x37 x67 : ℝ) : (((x36 + ((-1) * x67)) ≤ (-1)) ∨ ((x36 + ((-1) * x37)) ≥ 0) ∨ (¬ (x36 ≤ x37)) ∨ (¬ (x37 ≤ x67)) ∨ (¬ ((x67 - x36) ≥ 1)) ∨ (¬ ((x37 - x36) ≤ (t - 1))) ∨ (¬ ((x67 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th333 t x36 x37 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5850 (t x36 x37 x67 : ℝ) : (((x36 + ((-1) * x67)) ≤ (-1)) ∨ ((x36 + ((-1) * x67)) ≥ 1) ∨ (¬ (x36 ≤ x37)) ∨ (¬ (x37 ≤ x67)) ∨ (¬ ((x67 - x36) ≥ 1)) ∨ (¬ ((x37 - x36) ≤ (t - 1))) ∨ (¬ ((x67 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th333 t x36 x37 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5852 (t x36 x37 x67 : ℝ) : (((x36 + ((-1) * x67)) ≤ (-1)) ∨ ((t + ((-1) * x37) + x67) ≥ 1) ∨ (¬ (x36 ≤ x37)) ∨ (¬ (x37 ≤ x67)) ∨ (¬ ((x67 - x36) ≥ 1)) ∨ (¬ ((x37 - x36) ≤ (t - 1))) ∨ (¬ ((x67 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x37) + x67) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th333 t x36 x37 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5860 (t x36 x37 x67 : ℝ) : (((x36 + ((-1) * x67)) ≥ 1) ∨ ((t + x37 + ((-1) * x67)) ≥ 1) ∨ (¬ (x36 ≤ x37)) ∨ (¬ (x37 ≤ x67)) ∨ (¬ ((x67 - x36) ≥ 1)) ∨ (¬ ((x37 - x36) ≤ (t - 1))) ∨ (¬ ((x67 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x37 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th333 t x36 x37 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5863 (t x36 x37 x67 : ℝ) : (((x36 + ((-1) * x37)) ≤ 0) ∨ ((x37 + ((-1) * x67)) ≥ 0) ∨ (¬ (x67 ≤ x37)) ∨ (¬ (x37 ≤ x36)) ∨ (¬ ((x36 - x67) ≥ 1)) ∨ (¬ ((x36 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x37)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th333 t x36 x37 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5865 (t x36 x37 x67 : ℝ) : (((x36 + ((-1) * x67)) ≥ 1) ∨ ((x36 + ((-1) * x37)) ≤ 0) ∨ (¬ (x67 ≤ x37)) ∨ (¬ (x37 ≤ x36)) ∨ (¬ ((x36 - x67) ≥ 1)) ∨ (¬ ((x36 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 + ((-1) * x37)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th333 t x36 x37 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5870 (t x36 x37 x67 : ℝ) : (((x36 + ((-1) * x67)) ≥ 1) ∨ ((x37 + ((-1) * x67)) ≤ 0) ∨ (¬ (x67 ≤ x37)) ∨ (¬ (x37 ≤ x36)) ∨ (¬ ((x36 - x67) ≥ 1)) ∨ (¬ ((x36 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th333 t x36 x37 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5873 (t x36 x37 x67 : ℝ) : (((x36 + ((-1) * x67)) ≤ (-1)) ∨ ((x37 + ((-1) * x67)) ≥ 0) ∨ (¬ (x67 ≤ x37)) ∨ (¬ (x37 ≤ x36)) ∨ (¬ ((x36 - x67) ≥ 1)) ∨ (¬ ((x36 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th333 t x36 x37 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5874 (t x36 x37 x67 : ℝ) : (((x36 + ((-1) * x67)) ≤ (-1)) ∨ ((x36 + ((-1) * x37)) ≥ 0) ∨ (¬ (x67 ≤ x37)) ∨ (¬ (x37 ≤ x36)) ∨ (¬ ((x36 - x67) ≥ 1)) ∨ (¬ ((x36 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th333 t x36 x37 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5875 (t x36 x37 x67 : ℝ) : (((x36 + ((-1) * x67)) ≤ (-1)) ∨ ((x36 + ((-1) * x67)) ≥ 1) ∨ (¬ (x67 ≤ x37)) ∨ (¬ (x37 ≤ x36)) ∨ (¬ ((x36 - x67) ≥ 1)) ∨ (¬ ((x36 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th333 t x36 x37 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5877 (t x36 x37 x67 : ℝ) : (((x36 + ((-1) * x67)) ≤ (-1)) ∨ ((t + ((-1) * x37) + x67) ≥ 1) ∨ (¬ (x67 ≤ x37)) ∨ (¬ (x37 ≤ x36)) ∨ (¬ ((x36 - x67) ≥ 1)) ∨ (¬ ((x36 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x37) + x67) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th333 t x36 x37 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5883 (t x36 x37 x67 : ℝ) : (((t + x37 + ((-1) * x67)) ≥ 1) ∨ ((x37 + ((-1) * x67)) ≥ 0) ∨ (¬ (x67 ≤ x37)) ∨ (¬ (x37 ≤ x36)) ∨ (¬ ((x36 - x67) ≥ 1)) ∨ (¬ ((x36 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x37 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th333 t x36 x37 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5885 (t x36 x37 x67 : ℝ) : (((x36 + ((-1) * x67)) ≥ 1) ∨ ((t + x37 + ((-1) * x67)) ≥ 1) ∨ (¬ (x67 ≤ x37)) ∨ (¬ (x37 ≤ x36)) ∨ (¬ ((x36 - x67) ≥ 1)) ∨ (¬ ((x36 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x37 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th333 t x36 x37 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5938 (t x36 x37 x67 : ℝ) (h : (((x36 ≤ x37) ∧ (x37 ≤ x67) ∧ ((x67 - x36) ≥ 1) ∧ ((x37 - x36) ≤ (t - 1)) ∧ ((x67 - x37) ≤ (t - 1))) ∨ ((x67 ≤ x37) ∧ (x37 ≤ x36) ∧ ((x36 - x67) ≥ 1) ∧ ((x36 - x37) ≤ (t - 1)) ∧ ((x37 - x67) ≤ (t - 1))))) : ((x36 ≤ x37) ∨ (x67 ≤ x37)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x36 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x37) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5939 (t x36 x37 x67 : ℝ) (h : (((x36 ≤ x37) ∧ (x37 ≤ x67) ∧ ((x67 - x36) ≥ 1) ∧ ((x37 - x36) ≤ (t - 1)) ∧ ((x67 - x37) ≤ (t - 1))) ∨ ((x67 ≤ x37) ∧ (x37 ≤ x36) ∧ ((x36 - x67) ≥ 1) ∧ ((x36 - x37) ≤ (t - 1)) ∧ ((x37 - x67) ≤ (t - 1))))) : ((x36 ≤ x37) ∨ (x37 ≤ x36)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x36 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x36) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5940 (t x36 x37 x67 : ℝ) (h : (((x36 ≤ x37) ∧ (x37 ≤ x67) ∧ ((x67 - x36) ≥ 1) ∧ ((x37 - x36) ≤ (t - 1)) ∧ ((x67 - x37) ≤ (t - 1))) ∨ ((x67 ≤ x37) ∧ (x37 ≤ x36) ∧ ((x36 - x67) ≥ 1) ∧ ((x36 - x37) ≤ (t - 1)) ∧ ((x37 - x67) ≤ (t - 1))))) : ((x36 ≤ x37) ∨ ((x36 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x36 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5941 (t x36 x37 x67 : ℝ) (h : (((x36 ≤ x37) ∧ (x37 ≤ x67) ∧ ((x67 - x36) ≥ 1) ∧ ((x37 - x36) ≤ (t - 1)) ∧ ((x67 - x37) ≤ (t - 1))) ∨ ((x67 ≤ x37) ∧ (x37 ≤ x36) ∧ ((x36 - x67) ≥ 1) ∧ ((x36 - x37) ≤ (t - 1)) ∧ ((x37 - x67) ≤ (t - 1))))) : ((x36 ≤ x37) ∨ ((x36 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x36 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5942 (t x36 x37 x67 : ℝ) (h : (((x36 ≤ x37) ∧ (x37 ≤ x67) ∧ ((x67 - x36) ≥ 1) ∧ ((x37 - x36) ≤ (t - 1)) ∧ ((x67 - x37) ≤ (t - 1))) ∨ ((x67 ≤ x37) ∧ (x37 ≤ x36) ∧ ((x36 - x67) ≥ 1) ∧ ((x36 - x37) ≤ (t - 1)) ∧ ((x37 - x67) ≤ (t - 1))))) : ((x36 ≤ x37) ∨ ((x37 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x36 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5943 (t x36 x37 x67 : ℝ) (h : (((x36 ≤ x37) ∧ (x37 ≤ x67) ∧ ((x67 - x36) ≥ 1) ∧ ((x37 - x36) ≤ (t - 1)) ∧ ((x67 - x37) ≤ (t - 1))) ∨ ((x67 ≤ x37) ∧ (x37 ≤ x36) ∧ ((x36 - x67) ≥ 1) ∧ ((x36 - x37) ≤ (t - 1)) ∧ ((x37 - x67) ≤ (t - 1))))) : ((x37 ≤ x67) ∨ (x67 ≤ x37)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x37 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x37) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5944 (t x36 x37 x67 : ℝ) (h : (((x36 ≤ x37) ∧ (x37 ≤ x67) ∧ ((x67 - x36) ≥ 1) ∧ ((x37 - x36) ≤ (t - 1)) ∧ ((x67 - x37) ≤ (t - 1))) ∨ ((x67 ≤ x37) ∧ (x37 ≤ x36) ∧ ((x36 - x67) ≥ 1) ∧ ((x36 - x37) ≤ (t - 1)) ∧ ((x37 - x67) ≤ (t - 1))))) : ((x37 ≤ x67) ∨ (x37 ≤ x36)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x37 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x36) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5945 (t x36 x37 x67 : ℝ) (h : (((x36 ≤ x37) ∧ (x37 ≤ x67) ∧ ((x67 - x36) ≥ 1) ∧ ((x37 - x36) ≤ (t - 1)) ∧ ((x67 - x37) ≤ (t - 1))) ∨ ((x67 ≤ x37) ∧ (x37 ≤ x36) ∧ ((x36 - x67) ≥ 1) ∧ ((x36 - x37) ≤ (t - 1)) ∧ ((x37 - x67) ≤ (t - 1))))) : ((x37 ≤ x67) ∨ ((x36 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x37 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5946 (t x36 x37 x67 : ℝ) (h : (((x36 ≤ x37) ∧ (x37 ≤ x67) ∧ ((x67 - x36) ≥ 1) ∧ ((x37 - x36) ≤ (t - 1)) ∧ ((x67 - x37) ≤ (t - 1))) ∨ ((x67 ≤ x37) ∧ (x37 ≤ x36) ∧ ((x36 - x67) ≥ 1) ∧ ((x36 - x37) ≤ (t - 1)) ∧ ((x37 - x67) ≤ (t - 1))))) : ((x37 ≤ x67) ∨ ((x36 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x37 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5947 (t x36 x37 x67 : ℝ) (h : (((x36 ≤ x37) ∧ (x37 ≤ x67) ∧ ((x67 - x36) ≥ 1) ∧ ((x37 - x36) ≤ (t - 1)) ∧ ((x67 - x37) ≤ (t - 1))) ∨ ((x67 ≤ x37) ∧ (x37 ≤ x36) ∧ ((x36 - x67) ≥ 1) ∧ ((x36 - x37) ≤ (t - 1)) ∧ ((x37 - x67) ≤ (t - 1))))) : ((x37 ≤ x67) ∨ ((x37 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x37 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5948 (t x36 x37 x67 : ℝ) (h : (((x36 ≤ x37) ∧ (x37 ≤ x67) ∧ ((x67 - x36) ≥ 1) ∧ ((x37 - x36) ≤ (t - 1)) ∧ ((x67 - x37) ≤ (t - 1))) ∨ ((x67 ≤ x37) ∧ (x37 ≤ x36) ∧ ((x36 - x67) ≥ 1) ∧ ((x36 - x37) ≤ (t - 1)) ∧ ((x37 - x67) ≤ (t - 1))))) : (((x67 - x36) ≥ 1) ∨ (x67 ≤ x37)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x36) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x37) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5949 (t x36 x37 x67 : ℝ) (h : (((x36 ≤ x37) ∧ (x37 ≤ x67) ∧ ((x67 - x36) ≥ 1) ∧ ((x37 - x36) ≤ (t - 1)) ∧ ((x67 - x37) ≤ (t - 1))) ∨ ((x67 ≤ x37) ∧ (x37 ≤ x36) ∧ ((x36 - x67) ≥ 1) ∧ ((x36 - x37) ≤ (t - 1)) ∧ ((x37 - x67) ≤ (t - 1))))) : (((x67 - x36) ≥ 1) ∨ (x37 ≤ x36)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x36) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x36) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5950 (t x36 x37 x67 : ℝ) (h : (((x36 ≤ x37) ∧ (x37 ≤ x67) ∧ ((x67 - x36) ≥ 1) ∧ ((x37 - x36) ≤ (t - 1)) ∧ ((x67 - x37) ≤ (t - 1))) ∨ ((x67 ≤ x37) ∧ (x37 ≤ x36) ∧ ((x36 - x67) ≥ 1) ∧ ((x36 - x37) ≤ (t - 1)) ∧ ((x37 - x67) ≤ (t - 1))))) : (((x67 - x36) ≥ 1) ∨ ((x36 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x36) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5951 (t x36 x37 x67 : ℝ) (h : (((x36 ≤ x37) ∧ (x37 ≤ x67) ∧ ((x67 - x36) ≥ 1) ∧ ((x37 - x36) ≤ (t - 1)) ∧ ((x67 - x37) ≤ (t - 1))) ∨ ((x67 ≤ x37) ∧ (x37 ≤ x36) ∧ ((x36 - x67) ≥ 1) ∧ ((x36 - x37) ≤ (t - 1)) ∧ ((x37 - x67) ≤ (t - 1))))) : (((x67 - x36) ≥ 1) ∨ ((x36 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x36) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5952 (t x36 x37 x67 : ℝ) (h : (((x36 ≤ x37) ∧ (x37 ≤ x67) ∧ ((x67 - x36) ≥ 1) ∧ ((x37 - x36) ≤ (t - 1)) ∧ ((x67 - x37) ≤ (t - 1))) ∨ ((x67 ≤ x37) ∧ (x37 ≤ x36) ∧ ((x36 - x67) ≥ 1) ∧ ((x36 - x37) ≤ (t - 1)) ∧ ((x37 - x67) ≤ (t - 1))))) : (((x67 - x36) ≥ 1) ∨ ((x37 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x36) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5953 (t x36 x37 x67 : ℝ) (h : (((x36 ≤ x37) ∧ (x37 ≤ x67) ∧ ((x67 - x36) ≥ 1) ∧ ((x37 - x36) ≤ (t - 1)) ∧ ((x67 - x37) ≤ (t - 1))) ∨ ((x67 ≤ x37) ∧ (x37 ≤ x36) ∧ ((x36 - x67) ≥ 1) ∧ ((x36 - x37) ≤ (t - 1)) ∧ ((x37 - x67) ≤ (t - 1))))) : (((x37 - x36) ≤ (t - 1)) ∨ (x67 ≤ x37)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x36) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x37) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5954 (t x36 x37 x67 : ℝ) (h : (((x36 ≤ x37) ∧ (x37 ≤ x67) ∧ ((x67 - x36) ≥ 1) ∧ ((x37 - x36) ≤ (t - 1)) ∧ ((x67 - x37) ≤ (t - 1))) ∨ ((x67 ≤ x37) ∧ (x37 ≤ x36) ∧ ((x36 - x67) ≥ 1) ∧ ((x36 - x37) ≤ (t - 1)) ∧ ((x37 - x67) ≤ (t - 1))))) : (((x37 - x36) ≤ (t - 1)) ∨ (x37 ≤ x36)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x36) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x36) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5955 (t x36 x37 x67 : ℝ) (h : (((x36 ≤ x37) ∧ (x37 ≤ x67) ∧ ((x67 - x36) ≥ 1) ∧ ((x37 - x36) ≤ (t - 1)) ∧ ((x67 - x37) ≤ (t - 1))) ∨ ((x67 ≤ x37) ∧ (x37 ≤ x36) ∧ ((x36 - x67) ≥ 1) ∧ ((x36 - x37) ≤ (t - 1)) ∧ ((x37 - x67) ≤ (t - 1))))) : (((x37 - x36) ≤ (t - 1)) ∨ ((x36 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x36) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5956 (t x36 x37 x67 : ℝ) (h : (((x36 ≤ x37) ∧ (x37 ≤ x67) ∧ ((x67 - x36) ≥ 1) ∧ ((x37 - x36) ≤ (t - 1)) ∧ ((x67 - x37) ≤ (t - 1))) ∨ ((x67 ≤ x37) ∧ (x37 ≤ x36) ∧ ((x36 - x67) ≥ 1) ∧ ((x36 - x37) ≤ (t - 1)) ∧ ((x37 - x67) ≤ (t - 1))))) : (((x37 - x36) ≤ (t - 1)) ∨ ((x36 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x36) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5957 (t x36 x37 x67 : ℝ) (h : (((x36 ≤ x37) ∧ (x37 ≤ x67) ∧ ((x67 - x36) ≥ 1) ∧ ((x37 - x36) ≤ (t - 1)) ∧ ((x67 - x37) ≤ (t - 1))) ∨ ((x67 ≤ x37) ∧ (x37 ≤ x36) ∧ ((x36 - x67) ≥ 1) ∧ ((x36 - x37) ≤ (t - 1)) ∧ ((x37 - x67) ≤ (t - 1))))) : (((x37 - x36) ≤ (t - 1)) ∨ ((x37 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x36) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5958 (t x36 x37 x67 : ℝ) (h : (((x36 ≤ x37) ∧ (x37 ≤ x67) ∧ ((x67 - x36) ≥ 1) ∧ ((x37 - x36) ≤ (t - 1)) ∧ ((x67 - x37) ≤ (t - 1))) ∨ ((x67 ≤ x37) ∧ (x37 ≤ x36) ∧ ((x36 - x67) ≥ 1) ∧ ((x36 - x37) ≤ (t - 1)) ∧ ((x37 - x67) ≤ (t - 1))))) : (((x67 - x37) ≤ (t - 1)) ∨ (x67 ≤ x37)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x37) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x37) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5959 (t x36 x37 x67 : ℝ) (h : (((x36 ≤ x37) ∧ (x37 ≤ x67) ∧ ((x67 - x36) ≥ 1) ∧ ((x37 - x36) ≤ (t - 1)) ∧ ((x67 - x37) ≤ (t - 1))) ∨ ((x67 ≤ x37) ∧ (x37 ≤ x36) ∧ ((x36 - x67) ≥ 1) ∧ ((x36 - x37) ≤ (t - 1)) ∧ ((x37 - x67) ≤ (t - 1))))) : (((x67 - x37) ≤ (t - 1)) ∨ (x37 ≤ x36)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x37) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x36) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5960 (t x36 x37 x67 : ℝ) (h : (((x36 ≤ x37) ∧ (x37 ≤ x67) ∧ ((x67 - x36) ≥ 1) ∧ ((x37 - x36) ≤ (t - 1)) ∧ ((x67 - x37) ≤ (t - 1))) ∨ ((x67 ≤ x37) ∧ (x37 ≤ x36) ∧ ((x36 - x67) ≥ 1) ∧ ((x36 - x37) ≤ (t - 1)) ∧ ((x37 - x67) ≤ (t - 1))))) : (((x67 - x37) ≤ (t - 1)) ∨ ((x36 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x37) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5961 (t x36 x37 x67 : ℝ) (h : (((x36 ≤ x37) ∧ (x37 ≤ x67) ∧ ((x67 - x36) ≥ 1) ∧ ((x37 - x36) ≤ (t - 1)) ∧ ((x67 - x37) ≤ (t - 1))) ∨ ((x67 ≤ x37) ∧ (x37 ≤ x36) ∧ ((x36 - x67) ≥ 1) ∧ ((x36 - x37) ≤ (t - 1)) ∧ ((x37 - x67) ≤ (t - 1))))) : (((x67 - x37) ≤ (t - 1)) ∨ ((x36 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x37) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5962 (t x36 x37 x67 : ℝ) (h : (((x36 ≤ x37) ∧ (x37 ≤ x67) ∧ ((x67 - x36) ≥ 1) ∧ ((x37 - x36) ≤ (t - 1)) ∧ ((x67 - x37) ≤ (t - 1))) ∨ ((x67 ≤ x37) ∧ (x37 ≤ x36) ∧ ((x36 - x67) ≥ 1) ∧ ((x36 - x37) ≤ (t - 1)) ∧ ((x37 - x67) ≤ (t - 1))))) : (((x67 - x37) ≤ (t - 1)) ∨ ((x37 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x37) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5963 (t x02 x23 x24 x34 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((t + x34 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x34 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th335 t x02 x23 x24 x34 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u1 (And.intro u3 u2))))))) h

theorem clause5964 (x02 x23 x24 : ℝ) : ((¬ ((x23 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x23 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th336 x02 x23 x24
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u2 u1))) h

theorem clause5965 (x03 x23 x34 x36 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x34 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th337 x03 x23 x34 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u0 u2))))) h

theorem clause5973 (t x26 x28 x68 : ℝ) : (((x28 + ((-1) * x68)) ≤ 0) ∨ ((x26 + ((-1) * x68)) ≥ 1) ∨ (¬ (x26 ≤ x28)) ∨ (¬ (x28 ≤ x68)) ∨ (¬ ((x68 - x26) ≥ 1)) ∨ (¬ ((x28 - x26) ≤ (t - 1))) ∨ (¬ ((x68 - x28) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x28 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th341 t x26 x28 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5976 (t x26 x28 x68 : ℝ) : (((x26 + ((-1) * x68)) ≤ (-1)) ∨ ((x28 + ((-1) * x68)) ≥ 0) ∨ (¬ (x26 ≤ x28)) ∨ (¬ (x28 ≤ x68)) ∨ (¬ ((x68 - x26) ≥ 1)) ∨ (¬ ((x28 - x26) ≤ (t - 1))) ∨ (¬ ((x68 - x28) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 + ((-1) * x68)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x28 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th341 t x26 x28 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5978 (t x26 x28 x68 : ℝ) : (((x26 + ((-1) * x68)) ≤ (-1)) ∨ ((x26 + ((-1) * x68)) ≥ 1) ∨ (¬ (x26 ≤ x28)) ∨ (¬ (x28 ≤ x68)) ∨ (¬ ((x68 - x26) ≥ 1)) ∨ (¬ ((x28 - x26) ≤ (t - 1))) ∨ (¬ ((x68 - x28) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x28 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th341 t x26 x28 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5998 (t x26 x28 x68 : ℝ) : (((x28 + ((-1) * x68)) ≤ 0) ∨ ((x26 + ((-1) * x68)) ≥ 1) ∨ (¬ (x68 ≤ x28)) ∨ (¬ (x28 ≤ x26)) ∨ (¬ ((x26 - x68) ≥ 1)) ∨ (¬ ((x26 - x28) ≤ (t - 1))) ∨ (¬ ((x28 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x28 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th341 t x26 x28 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6001 (t x26 x28 x68 : ℝ) : (((x26 + ((-1) * x68)) ≤ (-1)) ∨ ((x28 + ((-1) * x68)) ≥ 0) ∨ (¬ (x68 ≤ x28)) ∨ (¬ (x28 ≤ x26)) ∨ (¬ ((x26 - x68) ≥ 1)) ∨ (¬ ((x26 - x28) ≤ (t - 1))) ∨ (¬ ((x28 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 + ((-1) * x68)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x28 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th341 t x26 x28 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6003 (t x26 x28 x68 : ℝ) : (((x26 + ((-1) * x68)) ≤ (-1)) ∨ ((x26 + ((-1) * x68)) ≥ 1) ∨ (¬ (x68 ≤ x28)) ∨ (¬ (x28 ≤ x26)) ∨ (¬ ((x26 - x68) ≥ 1)) ∨ (¬ ((x26 - x28) ≤ (t - 1))) ∨ (¬ ((x28 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x28 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th341 t x26 x28 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6066 (t x26 x28 x68 : ℝ) (h : (((x26 ≤ x28) ∧ (x28 ≤ x68) ∧ ((x68 - x26) ≥ 1) ∧ ((x28 - x26) ≤ (t - 1)) ∧ ((x68 - x28) ≤ (t - 1))) ∨ ((x68 ≤ x28) ∧ (x28 ≤ x26) ∧ ((x26 - x68) ≥ 1) ∧ ((x26 - x28) ≤ (t - 1)) ∧ ((x28 - x68) ≤ (t - 1))))) : ((x26 ≤ x28) ∨ (x68 ≤ x28)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x28) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6067 (t x26 x28 x68 : ℝ) (h : (((x26 ≤ x28) ∧ (x28 ≤ x68) ∧ ((x68 - x26) ≥ 1) ∧ ((x28 - x26) ≤ (t - 1)) ∧ ((x68 - x28) ≤ (t - 1))) ∨ ((x68 ≤ x28) ∧ (x28 ≤ x26) ∧ ((x26 - x68) ≥ 1) ∧ ((x26 - x28) ≤ (t - 1)) ∧ ((x28 - x68) ≤ (t - 1))))) : ((x26 ≤ x28) ∨ (x28 ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x26) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6068 (t x26 x28 x68 : ℝ) (h : (((x26 ≤ x28) ∧ (x28 ≤ x68) ∧ ((x68 - x26) ≥ 1) ∧ ((x28 - x26) ≤ (t - 1)) ∧ ((x68 - x28) ≤ (t - 1))) ∨ ((x68 ≤ x28) ∧ (x28 ≤ x26) ∧ ((x26 - x68) ≥ 1) ∧ ((x26 - x28) ≤ (t - 1)) ∧ ((x28 - x68) ≤ (t - 1))))) : ((x26 ≤ x28) ∨ ((x26 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6069 (t x26 x28 x68 : ℝ) (h : (((x26 ≤ x28) ∧ (x28 ≤ x68) ∧ ((x68 - x26) ≥ 1) ∧ ((x28 - x26) ≤ (t - 1)) ∧ ((x68 - x28) ≤ (t - 1))) ∨ ((x68 ≤ x28) ∧ (x28 ≤ x26) ∧ ((x26 - x68) ≥ 1) ∧ ((x26 - x28) ≤ (t - 1)) ∧ ((x28 - x68) ≤ (t - 1))))) : ((x26 ≤ x28) ∨ ((x26 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6070 (t x26 x28 x68 : ℝ) (h : (((x26 ≤ x28) ∧ (x28 ≤ x68) ∧ ((x68 - x26) ≥ 1) ∧ ((x28 - x26) ≤ (t - 1)) ∧ ((x68 - x28) ≤ (t - 1))) ∨ ((x68 ≤ x28) ∧ (x28 ≤ x26) ∧ ((x26 - x68) ≥ 1) ∧ ((x26 - x28) ≤ (t - 1)) ∧ ((x28 - x68) ≤ (t - 1))))) : ((x26 ≤ x28) ∨ ((x28 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6071 (t x26 x28 x68 : ℝ) (h : (((x26 ≤ x28) ∧ (x28 ≤ x68) ∧ ((x68 - x26) ≥ 1) ∧ ((x28 - x26) ≤ (t - 1)) ∧ ((x68 - x28) ≤ (t - 1))) ∨ ((x68 ≤ x28) ∧ (x28 ≤ x26) ∧ ((x26 - x68) ≥ 1) ∧ ((x26 - x28) ≤ (t - 1)) ∧ ((x28 - x68) ≤ (t - 1))))) : ((x28 ≤ x68) ∨ (x68 ≤ x28)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x28 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x28) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6072 (t x26 x28 x68 : ℝ) (h : (((x26 ≤ x28) ∧ (x28 ≤ x68) ∧ ((x68 - x26) ≥ 1) ∧ ((x28 - x26) ≤ (t - 1)) ∧ ((x68 - x28) ≤ (t - 1))) ∨ ((x68 ≤ x28) ∧ (x28 ≤ x26) ∧ ((x26 - x68) ≥ 1) ∧ ((x26 - x28) ≤ (t - 1)) ∧ ((x28 - x68) ≤ (t - 1))))) : ((x28 ≤ x68) ∨ (x28 ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x28 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x26) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6073 (t x26 x28 x68 : ℝ) (h : (((x26 ≤ x28) ∧ (x28 ≤ x68) ∧ ((x68 - x26) ≥ 1) ∧ ((x28 - x26) ≤ (t - 1)) ∧ ((x68 - x28) ≤ (t - 1))) ∨ ((x68 ≤ x28) ∧ (x28 ≤ x26) ∧ ((x26 - x68) ≥ 1) ∧ ((x26 - x28) ≤ (t - 1)) ∧ ((x28 - x68) ≤ (t - 1))))) : ((x28 ≤ x68) ∨ ((x26 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x28 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6074 (t x26 x28 x68 : ℝ) (h : (((x26 ≤ x28) ∧ (x28 ≤ x68) ∧ ((x68 - x26) ≥ 1) ∧ ((x28 - x26) ≤ (t - 1)) ∧ ((x68 - x28) ≤ (t - 1))) ∨ ((x68 ≤ x28) ∧ (x28 ≤ x26) ∧ ((x26 - x68) ≥ 1) ∧ ((x26 - x28) ≤ (t - 1)) ∧ ((x28 - x68) ≤ (t - 1))))) : ((x28 ≤ x68) ∨ ((x26 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x28 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6075 (t x26 x28 x68 : ℝ) (h : (((x26 ≤ x28) ∧ (x28 ≤ x68) ∧ ((x68 - x26) ≥ 1) ∧ ((x28 - x26) ≤ (t - 1)) ∧ ((x68 - x28) ≤ (t - 1))) ∨ ((x68 ≤ x28) ∧ (x28 ≤ x26) ∧ ((x26 - x68) ≥ 1) ∧ ((x26 - x28) ≤ (t - 1)) ∧ ((x28 - x68) ≤ (t - 1))))) : ((x28 ≤ x68) ∨ ((x28 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x28 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6076 (t x26 x28 x68 : ℝ) (h : (((x26 ≤ x28) ∧ (x28 ≤ x68) ∧ ((x68 - x26) ≥ 1) ∧ ((x28 - x26) ≤ (t - 1)) ∧ ((x68 - x28) ≤ (t - 1))) ∨ ((x68 ≤ x28) ∧ (x28 ≤ x26) ∧ ((x26 - x68) ≥ 1) ∧ ((x26 - x28) ≤ (t - 1)) ∧ ((x28 - x68) ≤ (t - 1))))) : (((x68 - x26) ≥ 1) ∨ (x68 ≤ x28)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x26) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x28) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6077 (t x26 x28 x68 : ℝ) (h : (((x26 ≤ x28) ∧ (x28 ≤ x68) ∧ ((x68 - x26) ≥ 1) ∧ ((x28 - x26) ≤ (t - 1)) ∧ ((x68 - x28) ≤ (t - 1))) ∨ ((x68 ≤ x28) ∧ (x28 ≤ x26) ∧ ((x26 - x68) ≥ 1) ∧ ((x26 - x28) ≤ (t - 1)) ∧ ((x28 - x68) ≤ (t - 1))))) : (((x68 - x26) ≥ 1) ∨ (x28 ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x26) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x26) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6078 (t x26 x28 x68 : ℝ) (h : (((x26 ≤ x28) ∧ (x28 ≤ x68) ∧ ((x68 - x26) ≥ 1) ∧ ((x28 - x26) ≤ (t - 1)) ∧ ((x68 - x28) ≤ (t - 1))) ∨ ((x68 ≤ x28) ∧ (x28 ≤ x26) ∧ ((x26 - x68) ≥ 1) ∧ ((x26 - x28) ≤ (t - 1)) ∧ ((x28 - x68) ≤ (t - 1))))) : (((x68 - x26) ≥ 1) ∨ ((x26 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x26) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6079 (t x26 x28 x68 : ℝ) (h : (((x26 ≤ x28) ∧ (x28 ≤ x68) ∧ ((x68 - x26) ≥ 1) ∧ ((x28 - x26) ≤ (t - 1)) ∧ ((x68 - x28) ≤ (t - 1))) ∨ ((x68 ≤ x28) ∧ (x28 ≤ x26) ∧ ((x26 - x68) ≥ 1) ∧ ((x26 - x28) ≤ (t - 1)) ∧ ((x28 - x68) ≤ (t - 1))))) : (((x68 - x26) ≥ 1) ∨ ((x26 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x26) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6080 (t x26 x28 x68 : ℝ) (h : (((x26 ≤ x28) ∧ (x28 ≤ x68) ∧ ((x68 - x26) ≥ 1) ∧ ((x28 - x26) ≤ (t - 1)) ∧ ((x68 - x28) ≤ (t - 1))) ∨ ((x68 ≤ x28) ∧ (x28 ≤ x26) ∧ ((x26 - x68) ≥ 1) ∧ ((x26 - x28) ≤ (t - 1)) ∧ ((x28 - x68) ≤ (t - 1))))) : (((x68 - x26) ≥ 1) ∨ ((x28 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x26) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6081 (t x26 x28 x68 : ℝ) (h : (((x26 ≤ x28) ∧ (x28 ≤ x68) ∧ ((x68 - x26) ≥ 1) ∧ ((x28 - x26) ≤ (t - 1)) ∧ ((x68 - x28) ≤ (t - 1))) ∨ ((x68 ≤ x28) ∧ (x28 ≤ x26) ∧ ((x26 - x68) ≥ 1) ∧ ((x26 - x28) ≤ (t - 1)) ∧ ((x28 - x68) ≤ (t - 1))))) : (((x28 - x26) ≤ (t - 1)) ∨ (x68 ≤ x28)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x26) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x28) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6082 (t x26 x28 x68 : ℝ) (h : (((x26 ≤ x28) ∧ (x28 ≤ x68) ∧ ((x68 - x26) ≥ 1) ∧ ((x28 - x26) ≤ (t - 1)) ∧ ((x68 - x28) ≤ (t - 1))) ∨ ((x68 ≤ x28) ∧ (x28 ≤ x26) ∧ ((x26 - x68) ≥ 1) ∧ ((x26 - x28) ≤ (t - 1)) ∧ ((x28 - x68) ≤ (t - 1))))) : (((x28 - x26) ≤ (t - 1)) ∨ (x28 ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x26) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x26) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6083 (t x26 x28 x68 : ℝ) (h : (((x26 ≤ x28) ∧ (x28 ≤ x68) ∧ ((x68 - x26) ≥ 1) ∧ ((x28 - x26) ≤ (t - 1)) ∧ ((x68 - x28) ≤ (t - 1))) ∨ ((x68 ≤ x28) ∧ (x28 ≤ x26) ∧ ((x26 - x68) ≥ 1) ∧ ((x26 - x28) ≤ (t - 1)) ∧ ((x28 - x68) ≤ (t - 1))))) : (((x28 - x26) ≤ (t - 1)) ∨ ((x26 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x26) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6084 (t x26 x28 x68 : ℝ) (h : (((x26 ≤ x28) ∧ (x28 ≤ x68) ∧ ((x68 - x26) ≥ 1) ∧ ((x28 - x26) ≤ (t - 1)) ∧ ((x68 - x28) ≤ (t - 1))) ∨ ((x68 ≤ x28) ∧ (x28 ≤ x26) ∧ ((x26 - x68) ≥ 1) ∧ ((x26 - x28) ≤ (t - 1)) ∧ ((x28 - x68) ≤ (t - 1))))) : (((x28 - x26) ≤ (t - 1)) ∨ ((x26 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x26) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6085 (t x26 x28 x68 : ℝ) (h : (((x26 ≤ x28) ∧ (x28 ≤ x68) ∧ ((x68 - x26) ≥ 1) ∧ ((x28 - x26) ≤ (t - 1)) ∧ ((x68 - x28) ≤ (t - 1))) ∨ ((x68 ≤ x28) ∧ (x28 ≤ x26) ∧ ((x26 - x68) ≥ 1) ∧ ((x26 - x28) ≤ (t - 1)) ∧ ((x28 - x68) ≤ (t - 1))))) : (((x28 - x26) ≤ (t - 1)) ∨ ((x28 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x26) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6086 (t x26 x28 x68 : ℝ) (h : (((x26 ≤ x28) ∧ (x28 ≤ x68) ∧ ((x68 - x26) ≥ 1) ∧ ((x28 - x26) ≤ (t - 1)) ∧ ((x68 - x28) ≤ (t - 1))) ∨ ((x68 ≤ x28) ∧ (x28 ≤ x26) ∧ ((x26 - x68) ≥ 1) ∧ ((x26 - x28) ≤ (t - 1)) ∧ ((x28 - x68) ≤ (t - 1))))) : (((x68 - x28) ≤ (t - 1)) ∨ (x68 ≤ x28)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x28) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x28) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6087 (t x26 x28 x68 : ℝ) (h : (((x26 ≤ x28) ∧ (x28 ≤ x68) ∧ ((x68 - x26) ≥ 1) ∧ ((x28 - x26) ≤ (t - 1)) ∧ ((x68 - x28) ≤ (t - 1))) ∨ ((x68 ≤ x28) ∧ (x28 ≤ x26) ∧ ((x26 - x68) ≥ 1) ∧ ((x26 - x28) ≤ (t - 1)) ∧ ((x28 - x68) ≤ (t - 1))))) : (((x68 - x28) ≤ (t - 1)) ∨ (x28 ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x28) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x26) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6088 (t x26 x28 x68 : ℝ) (h : (((x26 ≤ x28) ∧ (x28 ≤ x68) ∧ ((x68 - x26) ≥ 1) ∧ ((x28 - x26) ≤ (t - 1)) ∧ ((x68 - x28) ≤ (t - 1))) ∨ ((x68 ≤ x28) ∧ (x28 ≤ x26) ∧ ((x26 - x68) ≥ 1) ∧ ((x26 - x28) ≤ (t - 1)) ∧ ((x28 - x68) ≤ (t - 1))))) : (((x68 - x28) ≤ (t - 1)) ∨ ((x26 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x28) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6089 (t x26 x28 x68 : ℝ) (h : (((x26 ≤ x28) ∧ (x28 ≤ x68) ∧ ((x68 - x26) ≥ 1) ∧ ((x28 - x26) ≤ (t - 1)) ∧ ((x68 - x28) ≤ (t - 1))) ∨ ((x68 ≤ x28) ∧ (x28 ≤ x26) ∧ ((x26 - x68) ≥ 1) ∧ ((x26 - x28) ≤ (t - 1)) ∧ ((x28 - x68) ≤ (t - 1))))) : (((x68 - x28) ≤ (t - 1)) ∨ ((x26 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x28) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6090 (t x26 x28 x68 : ℝ) (h : (((x26 ≤ x28) ∧ (x28 ≤ x68) ∧ ((x68 - x26) ≥ 1) ∧ ((x28 - x26) ≤ (t - 1)) ∧ ((x68 - x28) ≤ (t - 1))) ∨ ((x68 ≤ x28) ∧ (x28 ≤ x26) ∧ ((x26 - x68) ≥ 1) ∧ ((x26 - x28) ≤ (t - 1)) ∧ ((x28 - x68) ≤ (t - 1))))) : (((x68 - x28) ≤ (t - 1)) ∨ ((x28 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x28) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6091 (t x04 x24 x26 x46 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((t + x04 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x26 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x04 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th343 t x04 x24 x26 x46 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u5 u3))))))) h

theorem clause6092 (x26 x46 x68 : ℝ) : ((¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x26 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x26 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x26 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th344 x26 x46 x68
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u2 u0))) h

theorem clause6094 (t x05 x35 x36 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((t + ((-1) * x05) + x35) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x05) + x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th348 t x05 x35 x36 x56 x67
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u4 (And.intro u0 (And.intro u2 (And.intro u5 u1)))))) h

theorem clause6095 (t x06 x35 x56 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((t + ((-1) * x06) + x56) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x57 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x06) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th350 t x06 x35 x56 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u1 (And.intro u4 u3))))))) h

theorem clause6096 (t x35 x37 x57 : ℝ) : (((x35 + ((-1) * x37)) ≤ 0) ∨ ((x37 + ((-1) * x57)) ≥ 0) ∨ (¬ (x35 ≤ x37)) ∨ (¬ (x37 ≤ x57)) ∨ (¬ ((x57 - x35) ≥ 1)) ∨ (¬ ((x37 - x35) ≤ (t - 1))) ∨ (¬ ((x57 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x37)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 + ((-1) * x57)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th352 t x35 x37 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6098 (t x35 x37 x57 : ℝ) : (((x35 + ((-1) * x57)) ≥ 1) ∨ ((x35 + ((-1) * x37)) ≤ 0) ∨ (¬ (x35 ≤ x37)) ∨ (¬ (x37 ≤ x57)) ∨ (¬ ((x57 - x35) ≥ 1)) ∨ (¬ ((x37 - x35) ≤ (t - 1))) ∨ (¬ ((x57 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x37)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th352 t x35 x37 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6103 (t x35 x37 x57 : ℝ) : (((x35 + ((-1) * x57)) ≥ 1) ∨ ((x37 + ((-1) * x57)) ≤ 0) ∨ (¬ (x35 ≤ x37)) ∨ (¬ (x37 ≤ x57)) ∨ (¬ ((x57 - x35) ≥ 1)) ∨ (¬ ((x37 - x35) ≤ (t - 1))) ∨ (¬ ((x57 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th352 t x35 x37 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6106 (t x35 x37 x57 : ℝ) : (((x35 + ((-1) * x57)) ≤ (-1)) ∨ ((x37 + ((-1) * x57)) ≥ 0) ∨ (¬ (x35 ≤ x37)) ∨ (¬ (x37 ≤ x57)) ∨ (¬ ((x57 - x35) ≥ 1)) ∨ (¬ ((x37 - x35) ≤ (t - 1))) ∨ (¬ ((x57 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 + ((-1) * x57)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th352 t x35 x37 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6107 (t x35 x37 x57 : ℝ) : (((x35 + ((-1) * x57)) ≤ (-1)) ∨ ((x35 + ((-1) * x37)) ≥ 0) ∨ (¬ (x35 ≤ x37)) ∨ (¬ (x37 ≤ x57)) ∨ (¬ ((x57 - x35) ≥ 1)) ∨ (¬ ((x37 - x35) ≤ (t - 1))) ∨ (¬ ((x57 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th352 t x35 x37 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6108 (t x35 x37 x57 : ℝ) : (((x35 + ((-1) * x57)) ≥ 1) ∨ ((x35 + ((-1) * x57)) ≤ (-1)) ∨ (¬ (x35 ≤ x37)) ∨ (¬ (x37 ≤ x57)) ∨ (¬ ((x57 - x35) ≥ 1)) ∨ (¬ ((x37 - x35) ≤ (t - 1))) ∨ (¬ ((x57 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th352 t x35 x37 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6110 (t x35 x37 x57 : ℝ) : (((x35 + ((-1) * x57)) ≤ (-1)) ∨ ((t + ((-1) * x37) + x57) ≥ 1) ∨ (¬ (x35 ≤ x37)) ∨ (¬ (x37 ≤ x57)) ∨ (¬ ((x57 - x35) ≥ 1)) ∨ (¬ ((x37 - x35) ≤ (t - 1))) ∨ (¬ ((x57 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x37) + x57) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th352 t x35 x37 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6112 (t x35 x37 x57 : ℝ) : (((t + x35 + ((-1) * x37)) ≥ 1) ∨ ((x35 + ((-1) * x37)) ≥ 0) ∨ (¬ (x35 ≤ x37)) ∨ (¬ (x37 ≤ x57)) ∨ (¬ ((x57 - x35) ≥ 1)) ∨ (¬ ((x37 - x35) ≤ (t - 1))) ∨ (¬ ((x57 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x35 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th352 t x35 x37 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6116 (t x35 x37 x57 : ℝ) : (((t + x37 + ((-1) * x57)) ≥ 1) ∨ ((x37 + ((-1) * x57)) ≥ 0) ∨ (¬ (x35 ≤ x37)) ∨ (¬ (x37 ≤ x57)) ∨ (¬ ((x57 - x35) ≥ 1)) ∨ (¬ ((x37 - x35) ≤ (t - 1))) ∨ (¬ ((x57 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x37 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 + ((-1) * x57)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th352 t x35 x37 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6118 (t x35 x37 x57 : ℝ) : (((x35 + ((-1) * x57)) ≥ 1) ∨ ((t + x37 + ((-1) * x57)) ≥ 1) ∨ (¬ (x35 ≤ x37)) ∨ (¬ (x37 ≤ x57)) ∨ (¬ ((x57 - x35) ≥ 1)) ∨ (¬ ((x37 - x35) ≤ (t - 1))) ∨ (¬ ((x57 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x37 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th352 t x35 x37 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6123 (t x35 x37 x57 : ℝ) : (((x35 + ((-1) * x57)) ≥ 1) ∨ ((x35 + ((-1) * x37)) ≤ 0) ∨ (¬ (x57 ≤ x37)) ∨ (¬ (x37 ≤ x35)) ∨ (¬ ((x35 - x57) ≥ 1)) ∨ (¬ ((x35 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x37)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th352 t x35 x37 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6127 (t x35 x37 x57 : ℝ) : (((x37 + ((-1) * x57)) ≤ 0) ∨ ((x35 + ((-1) * x37)) ≥ 0) ∨ (¬ (x57 ≤ x37)) ∨ (¬ (x37 ≤ x35)) ∨ (¬ ((x35 - x57) ≥ 1)) ∨ (¬ ((x35 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th352 t x35 x37 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6128 (t x35 x37 x57 : ℝ) : (((x35 + ((-1) * x57)) ≥ 1) ∨ ((x37 + ((-1) * x57)) ≤ 0) ∨ (¬ (x57 ≤ x37)) ∨ (¬ (x37 ≤ x35)) ∨ (¬ ((x35 - x57) ≥ 1)) ∨ (¬ ((x35 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th352 t x35 x37 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6131 (t x35 x37 x57 : ℝ) : (((x35 + ((-1) * x57)) ≤ (-1)) ∨ ((x37 + ((-1) * x57)) ≥ 0) ∨ (¬ (x57 ≤ x37)) ∨ (¬ (x37 ≤ x35)) ∨ (¬ ((x35 - x57) ≥ 1)) ∨ (¬ ((x35 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 + ((-1) * x57)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th352 t x35 x37 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6132 (t x35 x37 x57 : ℝ) : (((x35 + ((-1) * x57)) ≤ (-1)) ∨ ((x35 + ((-1) * x37)) ≥ 0) ∨ (¬ (x57 ≤ x37)) ∨ (¬ (x37 ≤ x35)) ∨ (¬ ((x35 - x57) ≥ 1)) ∨ (¬ ((x35 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th352 t x35 x37 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6133 (t x35 x37 x57 : ℝ) : (((x35 + ((-1) * x57)) ≥ 1) ∨ ((x35 + ((-1) * x57)) ≤ (-1)) ∨ (¬ (x57 ≤ x37)) ∨ (¬ (x37 ≤ x35)) ∨ (¬ ((x35 - x57) ≥ 1)) ∨ (¬ ((x35 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th352 t x35 x37 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6135 (t x35 x37 x57 : ℝ) : (((x35 + ((-1) * x57)) ≤ (-1)) ∨ ((t + ((-1) * x37) + x57) ≥ 1) ∨ (¬ (x57 ≤ x37)) ∨ (¬ (x37 ≤ x35)) ∨ (¬ ((x35 - x57) ≥ 1)) ∨ (¬ ((x35 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x37) + x57) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th352 t x35 x37 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6137 (t x35 x37 x57 : ℝ) : (((t + x35 + ((-1) * x37)) ≥ 1) ∨ ((x35 + ((-1) * x37)) ≥ 0) ∨ (¬ (x57 ≤ x37)) ∨ (¬ (x37 ≤ x35)) ∨ (¬ ((x35 - x57) ≥ 1)) ∨ (¬ ((x35 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x35 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th352 t x35 x37 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6143 (t x35 x37 x57 : ℝ) : (((x35 + ((-1) * x57)) ≥ 1) ∨ ((t + x37 + ((-1) * x57)) ≥ 1) ∨ (¬ (x57 ≤ x37)) ∨ (¬ (x37 ≤ x35)) ∨ (¬ ((x35 - x57) ≥ 1)) ∨ (¬ ((x35 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x37 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th352 t x35 x37 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6196 (t x35 x37 x57 : ℝ) (h : (((x35 ≤ x37) ∧ (x37 ≤ x57) ∧ ((x57 - x35) ≥ 1) ∧ ((x37 - x35) ≤ (t - 1)) ∧ ((x57 - x37) ≤ (t - 1))) ∨ ((x57 ≤ x37) ∧ (x37 ≤ x35) ∧ ((x35 - x57) ≥ 1) ∧ ((x35 - x37) ≤ (t - 1)) ∧ ((x37 - x57) ≤ (t - 1))))) : ((x35 ≤ x37) ∨ (x57 ≤ x37)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x35 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x37) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6197 (t x35 x37 x57 : ℝ) (h : (((x35 ≤ x37) ∧ (x37 ≤ x57) ∧ ((x57 - x35) ≥ 1) ∧ ((x37 - x35) ≤ (t - 1)) ∧ ((x57 - x37) ≤ (t - 1))) ∨ ((x57 ≤ x37) ∧ (x37 ≤ x35) ∧ ((x35 - x57) ≥ 1) ∧ ((x35 - x37) ≤ (t - 1)) ∧ ((x37 - x57) ≤ (t - 1))))) : ((x35 ≤ x37) ∨ (x37 ≤ x35)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x35 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x35) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6198 (t x35 x37 x57 : ℝ) (h : (((x35 ≤ x37) ∧ (x37 ≤ x57) ∧ ((x57 - x35) ≥ 1) ∧ ((x37 - x35) ≤ (t - 1)) ∧ ((x57 - x37) ≤ (t - 1))) ∨ ((x57 ≤ x37) ∧ (x37 ≤ x35) ∧ ((x35 - x57) ≥ 1) ∧ ((x35 - x37) ≤ (t - 1)) ∧ ((x37 - x57) ≤ (t - 1))))) : ((x35 ≤ x37) ∨ ((x35 - x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x35 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x57) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6199 (t x35 x37 x57 : ℝ) (h : (((x35 ≤ x37) ∧ (x37 ≤ x57) ∧ ((x57 - x35) ≥ 1) ∧ ((x37 - x35) ≤ (t - 1)) ∧ ((x57 - x37) ≤ (t - 1))) ∨ ((x57 ≤ x37) ∧ (x37 ≤ x35) ∧ ((x35 - x57) ≥ 1) ∧ ((x35 - x37) ≤ (t - 1)) ∧ ((x37 - x57) ≤ (t - 1))))) : ((x35 ≤ x37) ∨ ((x35 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x35 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6200 (t x35 x37 x57 : ℝ) (h : (((x35 ≤ x37) ∧ (x37 ≤ x57) ∧ ((x57 - x35) ≥ 1) ∧ ((x37 - x35) ≤ (t - 1)) ∧ ((x57 - x37) ≤ (t - 1))) ∨ ((x57 ≤ x37) ∧ (x37 ≤ x35) ∧ ((x35 - x57) ≥ 1) ∧ ((x35 - x37) ≤ (t - 1)) ∧ ((x37 - x57) ≤ (t - 1))))) : ((x35 ≤ x37) ∨ ((x37 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x35 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6201 (t x35 x37 x57 : ℝ) (h : (((x35 ≤ x37) ∧ (x37 ≤ x57) ∧ ((x57 - x35) ≥ 1) ∧ ((x37 - x35) ≤ (t - 1)) ∧ ((x57 - x37) ≤ (t - 1))) ∨ ((x57 ≤ x37) ∧ (x37 ≤ x35) ∧ ((x35 - x57) ≥ 1) ∧ ((x35 - x37) ≤ (t - 1)) ∧ ((x37 - x57) ≤ (t - 1))))) : ((x37 ≤ x57) ∨ (x57 ≤ x37)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x37 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x37) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6202 (t x35 x37 x57 : ℝ) (h : (((x35 ≤ x37) ∧ (x37 ≤ x57) ∧ ((x57 - x35) ≥ 1) ∧ ((x37 - x35) ≤ (t - 1)) ∧ ((x57 - x37) ≤ (t - 1))) ∨ ((x57 ≤ x37) ∧ (x37 ≤ x35) ∧ ((x35 - x57) ≥ 1) ∧ ((x35 - x37) ≤ (t - 1)) ∧ ((x37 - x57) ≤ (t - 1))))) : ((x37 ≤ x57) ∨ (x37 ≤ x35)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x37 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x35) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6203 (t x35 x37 x57 : ℝ) (h : (((x35 ≤ x37) ∧ (x37 ≤ x57) ∧ ((x57 - x35) ≥ 1) ∧ ((x37 - x35) ≤ (t - 1)) ∧ ((x57 - x37) ≤ (t - 1))) ∨ ((x57 ≤ x37) ∧ (x37 ≤ x35) ∧ ((x35 - x57) ≥ 1) ∧ ((x35 - x37) ≤ (t - 1)) ∧ ((x37 - x57) ≤ (t - 1))))) : ((x37 ≤ x57) ∨ ((x35 - x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x37 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x57) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6204 (t x35 x37 x57 : ℝ) (h : (((x35 ≤ x37) ∧ (x37 ≤ x57) ∧ ((x57 - x35) ≥ 1) ∧ ((x37 - x35) ≤ (t - 1)) ∧ ((x57 - x37) ≤ (t - 1))) ∨ ((x57 ≤ x37) ∧ (x37 ≤ x35) ∧ ((x35 - x57) ≥ 1) ∧ ((x35 - x37) ≤ (t - 1)) ∧ ((x37 - x57) ≤ (t - 1))))) : ((x37 ≤ x57) ∨ ((x35 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x37 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6205 (t x35 x37 x57 : ℝ) (h : (((x35 ≤ x37) ∧ (x37 ≤ x57) ∧ ((x57 - x35) ≥ 1) ∧ ((x37 - x35) ≤ (t - 1)) ∧ ((x57 - x37) ≤ (t - 1))) ∨ ((x57 ≤ x37) ∧ (x37 ≤ x35) ∧ ((x35 - x57) ≥ 1) ∧ ((x35 - x37) ≤ (t - 1)) ∧ ((x37 - x57) ≤ (t - 1))))) : ((x37 ≤ x57) ∨ ((x37 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x37 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6206 (t x35 x37 x57 : ℝ) (h : (((x35 ≤ x37) ∧ (x37 ≤ x57) ∧ ((x57 - x35) ≥ 1) ∧ ((x37 - x35) ≤ (t - 1)) ∧ ((x57 - x37) ≤ (t - 1))) ∨ ((x57 ≤ x37) ∧ (x37 ≤ x35) ∧ ((x35 - x57) ≥ 1) ∧ ((x35 - x37) ≤ (t - 1)) ∧ ((x37 - x57) ≤ (t - 1))))) : (((x57 - x35) ≥ 1) ∨ (x57 ≤ x37)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x35) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x37) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6207 (t x35 x37 x57 : ℝ) (h : (((x35 ≤ x37) ∧ (x37 ≤ x57) ∧ ((x57 - x35) ≥ 1) ∧ ((x37 - x35) ≤ (t - 1)) ∧ ((x57 - x37) ≤ (t - 1))) ∨ ((x57 ≤ x37) ∧ (x37 ≤ x35) ∧ ((x35 - x57) ≥ 1) ∧ ((x35 - x37) ≤ (t - 1)) ∧ ((x37 - x57) ≤ (t - 1))))) : (((x57 - x35) ≥ 1) ∨ (x37 ≤ x35)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x35) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x35) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6208 (t x35 x37 x57 : ℝ) (h : (((x35 ≤ x37) ∧ (x37 ≤ x57) ∧ ((x57 - x35) ≥ 1) ∧ ((x37 - x35) ≤ (t - 1)) ∧ ((x57 - x37) ≤ (t - 1))) ∨ ((x57 ≤ x37) ∧ (x37 ≤ x35) ∧ ((x35 - x57) ≥ 1) ∧ ((x35 - x37) ≤ (t - 1)) ∧ ((x37 - x57) ≤ (t - 1))))) : (((x57 - x35) ≥ 1) ∨ ((x35 - x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x35) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x57) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6209 (t x35 x37 x57 : ℝ) (h : (((x35 ≤ x37) ∧ (x37 ≤ x57) ∧ ((x57 - x35) ≥ 1) ∧ ((x37 - x35) ≤ (t - 1)) ∧ ((x57 - x37) ≤ (t - 1))) ∨ ((x57 ≤ x37) ∧ (x37 ≤ x35) ∧ ((x35 - x57) ≥ 1) ∧ ((x35 - x37) ≤ (t - 1)) ∧ ((x37 - x57) ≤ (t - 1))))) : (((x57 - x35) ≥ 1) ∨ ((x35 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x35) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6210 (t x35 x37 x57 : ℝ) (h : (((x35 ≤ x37) ∧ (x37 ≤ x57) ∧ ((x57 - x35) ≥ 1) ∧ ((x37 - x35) ≤ (t - 1)) ∧ ((x57 - x37) ≤ (t - 1))) ∨ ((x57 ≤ x37) ∧ (x37 ≤ x35) ∧ ((x35 - x57) ≥ 1) ∧ ((x35 - x37) ≤ (t - 1)) ∧ ((x37 - x57) ≤ (t - 1))))) : (((x57 - x35) ≥ 1) ∨ ((x37 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x35) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6211 (t x35 x37 x57 : ℝ) (h : (((x35 ≤ x37) ∧ (x37 ≤ x57) ∧ ((x57 - x35) ≥ 1) ∧ ((x37 - x35) ≤ (t - 1)) ∧ ((x57 - x37) ≤ (t - 1))) ∨ ((x57 ≤ x37) ∧ (x37 ≤ x35) ∧ ((x35 - x57) ≥ 1) ∧ ((x35 - x37) ≤ (t - 1)) ∧ ((x37 - x57) ≤ (t - 1))))) : (((x37 - x35) ≤ (t - 1)) ∨ (x57 ≤ x37)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x35) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x37) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6212 (t x35 x37 x57 : ℝ) (h : (((x35 ≤ x37) ∧ (x37 ≤ x57) ∧ ((x57 - x35) ≥ 1) ∧ ((x37 - x35) ≤ (t - 1)) ∧ ((x57 - x37) ≤ (t - 1))) ∨ ((x57 ≤ x37) ∧ (x37 ≤ x35) ∧ ((x35 - x57) ≥ 1) ∧ ((x35 - x37) ≤ (t - 1)) ∧ ((x37 - x57) ≤ (t - 1))))) : (((x37 - x35) ≤ (t - 1)) ∨ (x37 ≤ x35)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x35) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x35) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6213 (t x35 x37 x57 : ℝ) (h : (((x35 ≤ x37) ∧ (x37 ≤ x57) ∧ ((x57 - x35) ≥ 1) ∧ ((x37 - x35) ≤ (t - 1)) ∧ ((x57 - x37) ≤ (t - 1))) ∨ ((x57 ≤ x37) ∧ (x37 ≤ x35) ∧ ((x35 - x57) ≥ 1) ∧ ((x35 - x37) ≤ (t - 1)) ∧ ((x37 - x57) ≤ (t - 1))))) : (((x37 - x35) ≤ (t - 1)) ∨ ((x35 - x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x35) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x57) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6214 (t x35 x37 x57 : ℝ) (h : (((x35 ≤ x37) ∧ (x37 ≤ x57) ∧ ((x57 - x35) ≥ 1) ∧ ((x37 - x35) ≤ (t - 1)) ∧ ((x57 - x37) ≤ (t - 1))) ∨ ((x57 ≤ x37) ∧ (x37 ≤ x35) ∧ ((x35 - x57) ≥ 1) ∧ ((x35 - x37) ≤ (t - 1)) ∧ ((x37 - x57) ≤ (t - 1))))) : (((x37 - x35) ≤ (t - 1)) ∨ ((x35 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x35) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6215 (t x35 x37 x57 : ℝ) (h : (((x35 ≤ x37) ∧ (x37 ≤ x57) ∧ ((x57 - x35) ≥ 1) ∧ ((x37 - x35) ≤ (t - 1)) ∧ ((x57 - x37) ≤ (t - 1))) ∨ ((x57 ≤ x37) ∧ (x37 ≤ x35) ∧ ((x35 - x57) ≥ 1) ∧ ((x35 - x37) ≤ (t - 1)) ∧ ((x37 - x57) ≤ (t - 1))))) : (((x37 - x35) ≤ (t - 1)) ∨ ((x37 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x35) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6216 (t x35 x37 x57 : ℝ) (h : (((x35 ≤ x37) ∧ (x37 ≤ x57) ∧ ((x57 - x35) ≥ 1) ∧ ((x37 - x35) ≤ (t - 1)) ∧ ((x57 - x37) ≤ (t - 1))) ∨ ((x57 ≤ x37) ∧ (x37 ≤ x35) ∧ ((x35 - x57) ≥ 1) ∧ ((x35 - x37) ≤ (t - 1)) ∧ ((x37 - x57) ≤ (t - 1))))) : (((x57 - x37) ≤ (t - 1)) ∨ (x57 ≤ x37)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x37) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x37) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6217 (t x35 x37 x57 : ℝ) (h : (((x35 ≤ x37) ∧ (x37 ≤ x57) ∧ ((x57 - x35) ≥ 1) ∧ ((x37 - x35) ≤ (t - 1)) ∧ ((x57 - x37) ≤ (t - 1))) ∨ ((x57 ≤ x37) ∧ (x37 ≤ x35) ∧ ((x35 - x57) ≥ 1) ∧ ((x35 - x37) ≤ (t - 1)) ∧ ((x37 - x57) ≤ (t - 1))))) : (((x57 - x37) ≤ (t - 1)) ∨ (x37 ≤ x35)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x37) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x35) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6218 (t x35 x37 x57 : ℝ) (h : (((x35 ≤ x37) ∧ (x37 ≤ x57) ∧ ((x57 - x35) ≥ 1) ∧ ((x37 - x35) ≤ (t - 1)) ∧ ((x57 - x37) ≤ (t - 1))) ∨ ((x57 ≤ x37) ∧ (x37 ≤ x35) ∧ ((x35 - x57) ≥ 1) ∧ ((x35 - x37) ≤ (t - 1)) ∧ ((x37 - x57) ≤ (t - 1))))) : (((x57 - x37) ≤ (t - 1)) ∨ ((x35 - x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x37) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x57) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6219 (t x35 x37 x57 : ℝ) (h : (((x35 ≤ x37) ∧ (x37 ≤ x57) ∧ ((x57 - x35) ≥ 1) ∧ ((x37 - x35) ≤ (t - 1)) ∧ ((x57 - x37) ≤ (t - 1))) ∨ ((x57 ≤ x37) ∧ (x37 ≤ x35) ∧ ((x35 - x57) ≥ 1) ∧ ((x35 - x37) ≤ (t - 1)) ∧ ((x37 - x57) ≤ (t - 1))))) : (((x57 - x37) ≤ (t - 1)) ∨ ((x35 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x37) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6220 (t x35 x37 x57 : ℝ) (h : (((x35 ≤ x37) ∧ (x37 ≤ x57) ∧ ((x57 - x35) ≥ 1) ∧ ((x37 - x35) ≤ (t - 1)) ∧ ((x57 - x37) ≤ (t - 1))) ∨ ((x57 ≤ x37) ∧ (x37 ≤ x35) ∧ ((x35 - x57) ≥ 1) ∧ ((x35 - x37) ≤ (t - 1)) ∧ ((x37 - x57) ≤ (t - 1))))) : (((x57 - x37) ≤ (t - 1)) ∨ ((x37 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x37) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6221 (t x03 x05 x34 x35 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + x34 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x34 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th354 t x03 x05 x34 x35 x57
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u2 (And.intro u5 (And.intro u3 (And.intro u1 u0)))))) h

theorem clause6222 (x05 x35 x57 : ℝ) : ((¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th355 x05 x35 x57
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u0 u2))) h

theorem clause6225 (t x05 x07 x57 : ℝ) : (((x05 + ((-1) * x07)) ≤ 0) ∨ ((x05 + ((-1) * x57)) ≥ 1) ∨ (¬ (x05 ≤ x07)) ∨ (¬ (x07 ≤ x57)) ∨ (¬ ((x57 - x05) ≥ 1)) ∨ (¬ ((x07 - x05) ≤ (t - 1))) ∨ (¬ ((x57 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x07)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x05 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th357 t x05 x07 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6230 (t x05 x07 x57 : ℝ) : (((x07 + ((-1) * x57)) ≤ 0) ∨ ((x05 + ((-1) * x57)) ≥ 1) ∨ (¬ (x05 ≤ x07)) ∨ (¬ (x07 ≤ x57)) ∨ (¬ ((x57 - x05) ≥ 1)) ∨ (¬ ((x07 - x05) ≤ (t - 1))) ∨ (¬ ((x57 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x05 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th357 t x05 x07 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6233 (t x05 x07 x57 : ℝ) : (((x05 + ((-1) * x57)) ≤ (-1)) ∨ ((x07 + ((-1) * x57)) ≥ 0) ∨ (¬ (x05 ≤ x07)) ∨ (¬ (x07 ≤ x57)) ∨ (¬ ((x57 - x05) ≥ 1)) ∨ (¬ ((x07 - x05) ≤ (t - 1))) ∨ (¬ ((x57 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x57)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x05 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th357 t x05 x07 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6234 (t x05 x07 x57 : ℝ) : (((x05 + ((-1) * x07)) ≥ 0) ∨ ((x05 + ((-1) * x57)) ≤ (-1)) ∨ (¬ (x05 ≤ x07)) ∨ (¬ (x07 ≤ x57)) ∨ (¬ ((x57 - x05) ≥ 1)) ∨ (¬ ((x07 - x05) ≤ (t - 1))) ∨ (¬ ((x57 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x07)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x05 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th357 t x05 x07 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6235 (t x05 x07 x57 : ℝ) : (((x05 + ((-1) * x57)) ≤ (-1)) ∨ ((x05 + ((-1) * x57)) ≥ 1) ∨ (¬ (x05 ≤ x07)) ∨ (¬ (x07 ≤ x57)) ∨ (¬ ((x57 - x05) ≥ 1)) ∨ (¬ ((x07 - x05) ≤ (t - 1))) ∨ (¬ ((x57 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x05 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th357 t x05 x07 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6250 (t x05 x07 x57 : ℝ) : (((x05 + ((-1) * x07)) ≤ 0) ∨ ((x05 + ((-1) * x57)) ≥ 1) ∨ (¬ (x57 ≤ x07)) ∨ (¬ (x07 ≤ x05)) ∨ (¬ ((x05 - x57) ≥ 1)) ∨ (¬ ((x05 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x07)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th357 t x05 x07 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6255 (t x05 x07 x57 : ℝ) : (((x07 + ((-1) * x57)) ≤ 0) ∨ ((x05 + ((-1) * x57)) ≥ 1) ∨ (¬ (x57 ≤ x07)) ∨ (¬ (x07 ≤ x05)) ∨ (¬ ((x05 - x57) ≥ 1)) ∨ (¬ ((x05 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th357 t x05 x07 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6258 (t x05 x07 x57 : ℝ) : (((x05 + ((-1) * x57)) ≤ (-1)) ∨ ((x07 + ((-1) * x57)) ≥ 0) ∨ (¬ (x57 ≤ x07)) ∨ (¬ (x07 ≤ x05)) ∨ (¬ ((x05 - x57) ≥ 1)) ∨ (¬ ((x05 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x57)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th357 t x05 x07 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6259 (t x05 x07 x57 : ℝ) : (((x05 + ((-1) * x07)) ≥ 0) ∨ ((x05 + ((-1) * x57)) ≤ (-1)) ∨ (¬ (x57 ≤ x07)) ∨ (¬ (x07 ≤ x05)) ∨ (¬ ((x05 - x57) ≥ 1)) ∨ (¬ ((x05 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x07)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th357 t x05 x07 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6260 (t x05 x07 x57 : ℝ) : (((x05 + ((-1) * x57)) ≤ (-1)) ∨ ((x05 + ((-1) * x57)) ≥ 1) ∨ (¬ (x57 ≤ x07)) ∨ (¬ (x07 ≤ x05)) ∨ (¬ ((x05 - x57) ≥ 1)) ∨ (¬ ((x05 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th357 t x05 x07 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6323 (t x05 x07 x57 : ℝ) (h : (((x05 ≤ x07) ∧ (x07 ≤ x57) ∧ ((x57 - x05) ≥ 1) ∧ ((x07 - x05) ≤ (t - 1)) ∧ ((x57 - x07) ≤ (t - 1))) ∨ ((x57 ≤ x07) ∧ (x07 ≤ x05) ∧ ((x05 - x57) ≥ 1) ∧ ((x05 - x07) ≤ (t - 1)) ∧ ((x07 - x57) ≤ (t - 1))))) : ((x05 ≤ x07) ∨ (x57 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6324 (t x05 x07 x57 : ℝ) (h : (((x05 ≤ x07) ∧ (x07 ≤ x57) ∧ ((x57 - x05) ≥ 1) ∧ ((x07 - x05) ≤ (t - 1)) ∧ ((x57 - x07) ≤ (t - 1))) ∨ ((x57 ≤ x07) ∧ (x07 ≤ x05) ∧ ((x05 - x57) ≥ 1) ∧ ((x05 - x07) ≤ (t - 1)) ∧ ((x07 - x57) ≤ (t - 1))))) : ((x05 ≤ x07) ∨ (x07 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6325 (t x05 x07 x57 : ℝ) (h : (((x05 ≤ x07) ∧ (x07 ≤ x57) ∧ ((x57 - x05) ≥ 1) ∧ ((x07 - x05) ≤ (t - 1)) ∧ ((x57 - x07) ≤ (t - 1))) ∨ ((x57 ≤ x07) ∧ (x07 ≤ x05) ∧ ((x05 - x57) ≥ 1) ∧ ((x05 - x07) ≤ (t - 1)) ∧ ((x07 - x57) ≤ (t - 1))))) : ((x05 ≤ x07) ∨ ((x05 - x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x57) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6326 (t x05 x07 x57 : ℝ) (h : (((x05 ≤ x07) ∧ (x07 ≤ x57) ∧ ((x57 - x05) ≥ 1) ∧ ((x07 - x05) ≤ (t - 1)) ∧ ((x57 - x07) ≤ (t - 1))) ∨ ((x57 ≤ x07) ∧ (x07 ≤ x05) ∧ ((x05 - x57) ≥ 1) ∧ ((x05 - x07) ≤ (t - 1)) ∧ ((x07 - x57) ≤ (t - 1))))) : ((x05 ≤ x07) ∨ ((x05 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6327 (t x05 x07 x57 : ℝ) (h : (((x05 ≤ x07) ∧ (x07 ≤ x57) ∧ ((x57 - x05) ≥ 1) ∧ ((x07 - x05) ≤ (t - 1)) ∧ ((x57 - x07) ≤ (t - 1))) ∨ ((x57 ≤ x07) ∧ (x07 ≤ x05) ∧ ((x05 - x57) ≥ 1) ∧ ((x05 - x07) ≤ (t - 1)) ∧ ((x07 - x57) ≤ (t - 1))))) : ((x05 ≤ x07) ∨ ((x07 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6328 (t x05 x07 x57 : ℝ) (h : (((x05 ≤ x07) ∧ (x07 ≤ x57) ∧ ((x57 - x05) ≥ 1) ∧ ((x07 - x05) ≤ (t - 1)) ∧ ((x57 - x07) ≤ (t - 1))) ∨ ((x57 ≤ x07) ∧ (x07 ≤ x05) ∧ ((x05 - x57) ≥ 1) ∧ ((x05 - x07) ≤ (t - 1)) ∧ ((x07 - x57) ≤ (t - 1))))) : ((x07 ≤ x57) ∨ (x57 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6329 (t x05 x07 x57 : ℝ) (h : (((x05 ≤ x07) ∧ (x07 ≤ x57) ∧ ((x57 - x05) ≥ 1) ∧ ((x07 - x05) ≤ (t - 1)) ∧ ((x57 - x07) ≤ (t - 1))) ∨ ((x57 ≤ x07) ∧ (x07 ≤ x05) ∧ ((x05 - x57) ≥ 1) ∧ ((x05 - x07) ≤ (t - 1)) ∧ ((x07 - x57) ≤ (t - 1))))) : ((x07 ≤ x57) ∨ (x07 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6330 (t x05 x07 x57 : ℝ) (h : (((x05 ≤ x07) ∧ (x07 ≤ x57) ∧ ((x57 - x05) ≥ 1) ∧ ((x07 - x05) ≤ (t - 1)) ∧ ((x57 - x07) ≤ (t - 1))) ∨ ((x57 ≤ x07) ∧ (x07 ≤ x05) ∧ ((x05 - x57) ≥ 1) ∧ ((x05 - x07) ≤ (t - 1)) ∧ ((x07 - x57) ≤ (t - 1))))) : ((x07 ≤ x57) ∨ ((x05 - x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x57) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6331 (t x05 x07 x57 : ℝ) (h : (((x05 ≤ x07) ∧ (x07 ≤ x57) ∧ ((x57 - x05) ≥ 1) ∧ ((x07 - x05) ≤ (t - 1)) ∧ ((x57 - x07) ≤ (t - 1))) ∨ ((x57 ≤ x07) ∧ (x07 ≤ x05) ∧ ((x05 - x57) ≥ 1) ∧ ((x05 - x07) ≤ (t - 1)) ∧ ((x07 - x57) ≤ (t - 1))))) : ((x07 ≤ x57) ∨ ((x05 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6332 (t x05 x07 x57 : ℝ) (h : (((x05 ≤ x07) ∧ (x07 ≤ x57) ∧ ((x57 - x05) ≥ 1) ∧ ((x07 - x05) ≤ (t - 1)) ∧ ((x57 - x07) ≤ (t - 1))) ∨ ((x57 ≤ x07) ∧ (x07 ≤ x05) ∧ ((x05 - x57) ≥ 1) ∧ ((x05 - x07) ≤ (t - 1)) ∧ ((x07 - x57) ≤ (t - 1))))) : ((x07 ≤ x57) ∨ ((x07 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6333 (t x05 x07 x57 : ℝ) (h : (((x05 ≤ x07) ∧ (x07 ≤ x57) ∧ ((x57 - x05) ≥ 1) ∧ ((x07 - x05) ≤ (t - 1)) ∧ ((x57 - x07) ≤ (t - 1))) ∨ ((x57 ≤ x07) ∧ (x07 ≤ x05) ∧ ((x05 - x57) ≥ 1) ∧ ((x05 - x07) ≤ (t - 1)) ∧ ((x07 - x57) ≤ (t - 1))))) : (((x57 - x05) ≥ 1) ∨ (x57 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x05) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6334 (t x05 x07 x57 : ℝ) (h : (((x05 ≤ x07) ∧ (x07 ≤ x57) ∧ ((x57 - x05) ≥ 1) ∧ ((x07 - x05) ≤ (t - 1)) ∧ ((x57 - x07) ≤ (t - 1))) ∨ ((x57 ≤ x07) ∧ (x07 ≤ x05) ∧ ((x05 - x57) ≥ 1) ∧ ((x05 - x07) ≤ (t - 1)) ∧ ((x07 - x57) ≤ (t - 1))))) : (((x57 - x05) ≥ 1) ∨ (x07 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x05) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6335 (t x05 x07 x57 : ℝ) (h : (((x05 ≤ x07) ∧ (x07 ≤ x57) ∧ ((x57 - x05) ≥ 1) ∧ ((x07 - x05) ≤ (t - 1)) ∧ ((x57 - x07) ≤ (t - 1))) ∨ ((x57 ≤ x07) ∧ (x07 ≤ x05) ∧ ((x05 - x57) ≥ 1) ∧ ((x05 - x07) ≤ (t - 1)) ∧ ((x07 - x57) ≤ (t - 1))))) : (((x57 - x05) ≥ 1) ∨ ((x05 - x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x05) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x57) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6336 (t x05 x07 x57 : ℝ) (h : (((x05 ≤ x07) ∧ (x07 ≤ x57) ∧ ((x57 - x05) ≥ 1) ∧ ((x07 - x05) ≤ (t - 1)) ∧ ((x57 - x07) ≤ (t - 1))) ∨ ((x57 ≤ x07) ∧ (x07 ≤ x05) ∧ ((x05 - x57) ≥ 1) ∧ ((x05 - x07) ≤ (t - 1)) ∧ ((x07 - x57) ≤ (t - 1))))) : (((x57 - x05) ≥ 1) ∨ ((x05 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x05) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6337 (t x05 x07 x57 : ℝ) (h : (((x05 ≤ x07) ∧ (x07 ≤ x57) ∧ ((x57 - x05) ≥ 1) ∧ ((x07 - x05) ≤ (t - 1)) ∧ ((x57 - x07) ≤ (t - 1))) ∨ ((x57 ≤ x07) ∧ (x07 ≤ x05) ∧ ((x05 - x57) ≥ 1) ∧ ((x05 - x07) ≤ (t - 1)) ∧ ((x07 - x57) ≤ (t - 1))))) : (((x57 - x05) ≥ 1) ∨ ((x07 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x05) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6338 (t x05 x07 x57 : ℝ) (h : (((x05 ≤ x07) ∧ (x07 ≤ x57) ∧ ((x57 - x05) ≥ 1) ∧ ((x07 - x05) ≤ (t - 1)) ∧ ((x57 - x07) ≤ (t - 1))) ∨ ((x57 ≤ x07) ∧ (x07 ≤ x05) ∧ ((x05 - x57) ≥ 1) ∧ ((x05 - x07) ≤ (t - 1)) ∧ ((x07 - x57) ≤ (t - 1))))) : (((x07 - x05) ≤ (t - 1)) ∨ (x57 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6339 (t x05 x07 x57 : ℝ) (h : (((x05 ≤ x07) ∧ (x07 ≤ x57) ∧ ((x57 - x05) ≥ 1) ∧ ((x07 - x05) ≤ (t - 1)) ∧ ((x57 - x07) ≤ (t - 1))) ∨ ((x57 ≤ x07) ∧ (x07 ≤ x05) ∧ ((x05 - x57) ≥ 1) ∧ ((x05 - x07) ≤ (t - 1)) ∧ ((x07 - x57) ≤ (t - 1))))) : (((x07 - x05) ≤ (t - 1)) ∨ (x07 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6340 (t x05 x07 x57 : ℝ) (h : (((x05 ≤ x07) ∧ (x07 ≤ x57) ∧ ((x57 - x05) ≥ 1) ∧ ((x07 - x05) ≤ (t - 1)) ∧ ((x57 - x07) ≤ (t - 1))) ∨ ((x57 ≤ x07) ∧ (x07 ≤ x05) ∧ ((x05 - x57) ≥ 1) ∧ ((x05 - x07) ≤ (t - 1)) ∧ ((x07 - x57) ≤ (t - 1))))) : (((x07 - x05) ≤ (t - 1)) ∨ ((x05 - x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x57) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6341 (t x05 x07 x57 : ℝ) (h : (((x05 ≤ x07) ∧ (x07 ≤ x57) ∧ ((x57 - x05) ≥ 1) ∧ ((x07 - x05) ≤ (t - 1)) ∧ ((x57 - x07) ≤ (t - 1))) ∨ ((x57 ≤ x07) ∧ (x07 ≤ x05) ∧ ((x05 - x57) ≥ 1) ∧ ((x05 - x07) ≤ (t - 1)) ∧ ((x07 - x57) ≤ (t - 1))))) : (((x07 - x05) ≤ (t - 1)) ∨ ((x05 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6342 (t x05 x07 x57 : ℝ) (h : (((x05 ≤ x07) ∧ (x07 ≤ x57) ∧ ((x57 - x05) ≥ 1) ∧ ((x07 - x05) ≤ (t - 1)) ∧ ((x57 - x07) ≤ (t - 1))) ∨ ((x57 ≤ x07) ∧ (x07 ≤ x05) ∧ ((x05 - x57) ≥ 1) ∧ ((x05 - x07) ≤ (t - 1)) ∧ ((x07 - x57) ≤ (t - 1))))) : (((x07 - x05) ≤ (t - 1)) ∨ ((x07 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6343 (t x05 x07 x57 : ℝ) (h : (((x05 ≤ x07) ∧ (x07 ≤ x57) ∧ ((x57 - x05) ≥ 1) ∧ ((x07 - x05) ≤ (t - 1)) ∧ ((x57 - x07) ≤ (t - 1))) ∨ ((x57 ≤ x07) ∧ (x07 ≤ x05) ∧ ((x05 - x57) ≥ 1) ∧ ((x05 - x07) ≤ (t - 1)) ∧ ((x07 - x57) ≤ (t - 1))))) : (((x57 - x07) ≤ (t - 1)) ∨ (x57 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6344 (t x05 x07 x57 : ℝ) (h : (((x05 ≤ x07) ∧ (x07 ≤ x57) ∧ ((x57 - x05) ≥ 1) ∧ ((x07 - x05) ≤ (t - 1)) ∧ ((x57 - x07) ≤ (t - 1))) ∨ ((x57 ≤ x07) ∧ (x07 ≤ x05) ∧ ((x05 - x57) ≥ 1) ∧ ((x05 - x07) ≤ (t - 1)) ∧ ((x07 - x57) ≤ (t - 1))))) : (((x57 - x07) ≤ (t - 1)) ∨ (x07 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6345 (t x05 x07 x57 : ℝ) (h : (((x05 ≤ x07) ∧ (x07 ≤ x57) ∧ ((x57 - x05) ≥ 1) ∧ ((x07 - x05) ≤ (t - 1)) ∧ ((x57 - x07) ≤ (t - 1))) ∨ ((x57 ≤ x07) ∧ (x07 ≤ x05) ∧ ((x05 - x57) ≥ 1) ∧ ((x05 - x07) ≤ (t - 1)) ∧ ((x07 - x57) ≤ (t - 1))))) : (((x57 - x07) ≤ (t - 1)) ∨ ((x05 - x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x57) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6346 (t x05 x07 x57 : ℝ) (h : (((x05 ≤ x07) ∧ (x07 ≤ x57) ∧ ((x57 - x05) ≥ 1) ∧ ((x07 - x05) ≤ (t - 1)) ∧ ((x57 - x07) ≤ (t - 1))) ∨ ((x57 ≤ x07) ∧ (x07 ≤ x05) ∧ ((x05 - x57) ≥ 1) ∧ ((x05 - x07) ≤ (t - 1)) ∧ ((x07 - x57) ≤ (t - 1))))) : (((x57 - x07) ≤ (t - 1)) ∨ ((x05 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6347 (t x05 x07 x57 : ℝ) (h : (((x05 ≤ x07) ∧ (x07 ≤ x57) ∧ ((x57 - x05) ≥ 1) ∧ ((x07 - x05) ≤ (t - 1)) ∧ ((x57 - x07) ≤ (t - 1))) ∨ ((x57 ≤ x07) ∧ (x07 ≤ x05) ∧ ((x05 - x57) ≥ 1) ∧ ((x05 - x07) ≤ (t - 1)) ∧ ((x07 - x57) ≤ (t - 1))))) : (((x57 - x07) ≤ (t - 1)) ∨ ((x07 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6348 (t x01 x05 x13 x15 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x13) + x15) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x13) + x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th359 t x01 x05 x13 x15 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u4 u5))))))) h

theorem clause6349 (x45 x57 : ℝ) : ((¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th361 x45 x57
  exact (fun hh => (Or.elim hh (fun hh => hh u0) (fun zz => ((fun hh => hh u1) zz)))) h

theorem clause6350 (t x45 x47 x57 : ℝ) : (((x45 + ((-1) * x47)) ≤ 0) ∨ ((x47 + ((-1) * x57)) ≥ 0) ∨ (¬ (x45 ≤ x47)) ∨ (¬ (x47 ≤ x57)) ∨ (¬ ((x57 - x45) ≥ 1)) ∨ (¬ ((x47 - x45) ≤ (t - 1))) ∨ (¬ ((x57 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 + ((-1) * x57)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6352 (t x45 x47 x57 : ℝ) : (((x45 + ((-1) * x57)) ≥ 1) ∨ ((x45 + ((-1) * x47)) ≤ 0) ∨ (¬ (x45 ≤ x47)) ∨ (¬ (x47 ≤ x57)) ∨ (¬ ((x57 - x45) ≥ 1)) ∨ (¬ ((x47 - x45) ≤ (t - 1))) ∨ (¬ ((x57 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6353 (t x45 x47 x57 : ℝ) : (((x45 + ((-1) * x47)) ≤ 0) ∨ ((t + ((-1) * x45) + x47) ≥ 1) ∨ (¬ (x45 ≤ x47)) ∨ (¬ (x47 ≤ x57)) ∨ (¬ ((x57 - x45) ≥ 1)) ∨ (¬ ((x47 - x45) ≤ (t - 1))) ∨ (¬ ((x57 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x45) + x47) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6356 (t x45 x47 x57 : ℝ) : (((x47 + ((-1) * x57)) ≤ 0) ∨ ((x45 + ((-1) * x47)) ≥ 0) ∨ (¬ (x45 ≤ x47)) ∨ (¬ (x47 ≤ x57)) ∨ (¬ ((x57 - x45) ≥ 1)) ∨ (¬ ((x47 - x45) ≤ (t - 1))) ∨ (¬ ((x57 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x47)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6357 (t x45 x47 x57 : ℝ) : (((x45 + ((-1) * x57)) ≥ 1) ∨ ((x47 + ((-1) * x57)) ≤ 0) ∨ (¬ (x45 ≤ x47)) ∨ (¬ (x47 ≤ x57)) ∨ (¬ ((x57 - x45) ≥ 1)) ∨ (¬ ((x47 - x45) ≤ (t - 1))) ∨ (¬ ((x57 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6360 (t x45 x47 x57 : ℝ) : (((x45 + ((-1) * x57)) ≤ (-1)) ∨ ((x47 + ((-1) * x57)) ≥ 0) ∨ (¬ (x45 ≤ x47)) ∨ (¬ (x47 ≤ x57)) ∨ (¬ ((x57 - x45) ≥ 1)) ∨ (¬ ((x47 - x45) ≤ (t - 1))) ∨ (¬ ((x57 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 + ((-1) * x57)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6362 (t x45 x47 x57 : ℝ) : (((x45 + ((-1) * x57)) ≤ (-1)) ∨ ((x45 + ((-1) * x57)) ≥ 1) ∨ (¬ (x45 ≤ x47)) ∨ (¬ (x47 ≤ x57)) ∨ (¬ ((x57 - x45) ≥ 1)) ∨ (¬ ((x47 - x45) ≤ (t - 1))) ∨ (¬ ((x57 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6363 (t x45 x47 x57 : ℝ) : (((x45 + ((-1) * x57)) ≤ (-1)) ∨ ((t + ((-1) * x45) + x47) ≥ 1) ∨ (¬ (x45 ≤ x47)) ∨ (¬ (x47 ≤ x57)) ∨ (¬ ((x57 - x45) ≥ 1)) ∨ (¬ ((x47 - x45) ≤ (t - 1))) ∨ (¬ ((x57 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x45) + x47) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6364 (t x45 x47 x57 : ℝ) : (((t + ((-1) * x47) + x57) ≥ 1) ∨ ((x45 + ((-1) * x57)) ≤ (-1)) ∨ (¬ (x45 ≤ x47)) ∨ (¬ (x47 ≤ x57)) ∨ (¬ ((x57 - x45) ≥ 1)) ∨ (¬ ((x47 - x45) ≤ (t - 1))) ∨ (¬ ((x57 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x47) + x57) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6366 (t x45 x47 x57 : ℝ) : (((t + x45 + ((-1) * x47)) ≥ 1) ∨ ((x45 + ((-1) * x47)) ≥ 0) ∨ (¬ (x45 ≤ x47)) ∨ (¬ (x47 ≤ x57)) ∨ (¬ ((x57 - x45) ≥ 1)) ∨ (¬ ((x47 - x45) ≤ (t - 1))) ∨ (¬ ((x57 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x45 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x47)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6367 (t x45 x47 x57 : ℝ) : (((x45 + ((-1) * x57)) ≥ 1) ∨ ((t + x45 + ((-1) * x47)) ≥ 1) ∨ (¬ (x45 ≤ x47)) ∨ (¬ (x47 ≤ x57)) ∨ (¬ ((x57 - x45) ≥ 1)) ∨ (¬ ((x47 - x45) ≤ (t - 1))) ∨ (¬ ((x57 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x45 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6370 (t x45 x47 x57 : ℝ) : (((t + x47 + ((-1) * x57)) ≥ 1) ∨ ((x47 + ((-1) * x57)) ≥ 0) ∨ (¬ (x45 ≤ x47)) ∨ (¬ (x47 ≤ x57)) ∨ (¬ ((x57 - x45) ≥ 1)) ∨ (¬ ((x47 - x45) ≤ (t - 1))) ∨ (¬ ((x57 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x47 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 + ((-1) * x57)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6372 (t x45 x47 x57 : ℝ) : (((x45 + ((-1) * x57)) ≥ 1) ∨ ((t + x47 + ((-1) * x57)) ≥ 1) ∨ (¬ (x45 ≤ x47)) ∨ (¬ (x47 ≤ x57)) ∨ (¬ ((x57 - x45) ≥ 1)) ∨ (¬ ((x47 - x45) ≤ (t - 1))) ∨ (¬ ((x57 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x47 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6375 (t x45 x47 x57 : ℝ) : (((x45 + ((-1) * x47)) ≤ 0) ∨ ((x47 + ((-1) * x57)) ≥ 0) ∨ (¬ (x57 ≤ x47)) ∨ (¬ (x47 ≤ x45)) ∨ (¬ ((x45 - x57) ≥ 1)) ∨ (¬ ((x45 - x47) ≤ (t - 1))) ∨ (¬ ((x47 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 + ((-1) * x57)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6377 (t x45 x47 x57 : ℝ) : (((x45 + ((-1) * x57)) ≥ 1) ∨ ((x45 + ((-1) * x47)) ≤ 0) ∨ (¬ (x57 ≤ x47)) ∨ (¬ (x47 ≤ x45)) ∨ (¬ ((x45 - x57) ≥ 1)) ∨ (¬ ((x45 - x47) ≤ (t - 1))) ∨ (¬ ((x47 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6378 (t x45 x47 x57 : ℝ) : (((x45 + ((-1) * x47)) ≤ 0) ∨ ((t + ((-1) * x45) + x47) ≥ 1) ∨ (¬ (x57 ≤ x47)) ∨ (¬ (x47 ≤ x45)) ∨ (¬ ((x45 - x57) ≥ 1)) ∨ (¬ ((x45 - x47) ≤ (t - 1))) ∨ (¬ ((x47 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x45) + x47) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6381 (t x45 x47 x57 : ℝ) : (((x47 + ((-1) * x57)) ≤ 0) ∨ ((x45 + ((-1) * x47)) ≥ 0) ∨ (¬ (x57 ≤ x47)) ∨ (¬ (x47 ≤ x45)) ∨ (¬ ((x45 - x57) ≥ 1)) ∨ (¬ ((x45 - x47) ≤ (t - 1))) ∨ (¬ ((x47 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x47)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6382 (t x45 x47 x57 : ℝ) : (((x45 + ((-1) * x57)) ≥ 1) ∨ ((x47 + ((-1) * x57)) ≤ 0) ∨ (¬ (x57 ≤ x47)) ∨ (¬ (x47 ≤ x45)) ∨ (¬ ((x45 - x57) ≥ 1)) ∨ (¬ ((x45 - x47) ≤ (t - 1))) ∨ (¬ ((x47 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6385 (t x45 x47 x57 : ℝ) : (((x45 + ((-1) * x57)) ≤ (-1)) ∨ ((x47 + ((-1) * x57)) ≥ 0) ∨ (¬ (x57 ≤ x47)) ∨ (¬ (x47 ≤ x45)) ∨ (¬ ((x45 - x57) ≥ 1)) ∨ (¬ ((x45 - x47) ≤ (t - 1))) ∨ (¬ ((x47 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 + ((-1) * x57)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6387 (t x45 x47 x57 : ℝ) : (((x45 + ((-1) * x57)) ≤ (-1)) ∨ ((x45 + ((-1) * x57)) ≥ 1) ∨ (¬ (x57 ≤ x47)) ∨ (¬ (x47 ≤ x45)) ∨ (¬ ((x45 - x57) ≥ 1)) ∨ (¬ ((x45 - x47) ≤ (t - 1))) ∨ (¬ ((x47 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6388 (t x45 x47 x57 : ℝ) : (((x45 + ((-1) * x57)) ≤ (-1)) ∨ ((t + ((-1) * x45) + x47) ≥ 1) ∨ (¬ (x57 ≤ x47)) ∨ (¬ (x47 ≤ x45)) ∨ (¬ ((x45 - x57) ≥ 1)) ∨ (¬ ((x45 - x47) ≤ (t - 1))) ∨ (¬ ((x47 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x45) + x47) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6389 (t x45 x47 x57 : ℝ) : (((t + ((-1) * x47) + x57) ≥ 1) ∨ ((x45 + ((-1) * x57)) ≤ (-1)) ∨ (¬ (x57 ≤ x47)) ∨ (¬ (x47 ≤ x45)) ∨ (¬ ((x45 - x57) ≥ 1)) ∨ (¬ ((x45 - x47) ≤ (t - 1))) ∨ (¬ ((x47 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x47) + x57) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6391 (t x45 x47 x57 : ℝ) : (((t + x45 + ((-1) * x47)) ≥ 1) ∨ ((x45 + ((-1) * x47)) ≥ 0) ∨ (¬ (x57 ≤ x47)) ∨ (¬ (x47 ≤ x45)) ∨ (¬ ((x45 - x57) ≥ 1)) ∨ (¬ ((x45 - x47) ≤ (t - 1))) ∨ (¬ ((x47 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x45 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x47)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6392 (t x45 x47 x57 : ℝ) : (((x45 + ((-1) * x57)) ≥ 1) ∨ ((t + x45 + ((-1) * x47)) ≥ 1) ∨ (¬ (x57 ≤ x47)) ∨ (¬ (x47 ≤ x45)) ∨ (¬ ((x45 - x57) ≥ 1)) ∨ (¬ ((x45 - x47) ≤ (t - 1))) ∨ (¬ ((x47 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x45 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6395 (t x45 x47 x57 : ℝ) : (((t + x47 + ((-1) * x57)) ≥ 1) ∨ ((x47 + ((-1) * x57)) ≥ 0) ∨ (¬ (x57 ≤ x47)) ∨ (¬ (x47 ≤ x45)) ∨ (¬ ((x45 - x57) ≥ 1)) ∨ (¬ ((x45 - x47) ≤ (t - 1))) ∨ (¬ ((x47 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x47 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 + ((-1) * x57)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6397 (t x45 x47 x57 : ℝ) : (((x45 + ((-1) * x57)) ≥ 1) ∨ ((t + x47 + ((-1) * x57)) ≥ 1) ∨ (¬ (x57 ≤ x47)) ∨ (¬ (x47 ≤ x45)) ∨ (¬ ((x45 - x57) ≥ 1)) ∨ (¬ ((x45 - x47) ≤ (t - 1))) ∨ (¬ ((x47 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x47 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th363 t x45 x47 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6450 (t x45 x47 x57 : ℝ) (h : (((x45 ≤ x47) ∧ (x47 ≤ x57) ∧ ((x57 - x45) ≥ 1) ∧ ((x47 - x45) ≤ (t - 1)) ∧ ((x57 - x47) ≤ (t - 1))) ∨ ((x57 ≤ x47) ∧ (x47 ≤ x45) ∧ ((x45 - x57) ≥ 1) ∧ ((x45 - x47) ≤ (t - 1)) ∧ ((x47 - x57) ≤ (t - 1))))) : ((x45 ≤ x47) ∨ (x57 ≤ x47)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x45 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x47) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6451 (t x45 x47 x57 : ℝ) (h : (((x45 ≤ x47) ∧ (x47 ≤ x57) ∧ ((x57 - x45) ≥ 1) ∧ ((x47 - x45) ≤ (t - 1)) ∧ ((x57 - x47) ≤ (t - 1))) ∨ ((x57 ≤ x47) ∧ (x47 ≤ x45) ∧ ((x45 - x57) ≥ 1) ∧ ((x45 - x47) ≤ (t - 1)) ∧ ((x47 - x57) ≤ (t - 1))))) : ((x45 ≤ x47) ∨ (x47 ≤ x45)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x45 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x45) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6452 (t x45 x47 x57 : ℝ) (h : (((x45 ≤ x47) ∧ (x47 ≤ x57) ∧ ((x57 - x45) ≥ 1) ∧ ((x47 - x45) ≤ (t - 1)) ∧ ((x57 - x47) ≤ (t - 1))) ∨ ((x57 ≤ x47) ∧ (x47 ≤ x45) ∧ ((x45 - x57) ≥ 1) ∧ ((x45 - x47) ≤ (t - 1)) ∧ ((x47 - x57) ≤ (t - 1))))) : ((x45 ≤ x47) ∨ ((x45 - x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x45 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x57) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6453 (t x45 x47 x57 : ℝ) (h : (((x45 ≤ x47) ∧ (x47 ≤ x57) ∧ ((x57 - x45) ≥ 1) ∧ ((x47 - x45) ≤ (t - 1)) ∧ ((x57 - x47) ≤ (t - 1))) ∨ ((x57 ≤ x47) ∧ (x47 ≤ x45) ∧ ((x45 - x57) ≥ 1) ∧ ((x45 - x47) ≤ (t - 1)) ∧ ((x47 - x57) ≤ (t - 1))))) : ((x45 ≤ x47) ∨ ((x45 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x45 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6454 (t x45 x47 x57 : ℝ) (h : (((x45 ≤ x47) ∧ (x47 ≤ x57) ∧ ((x57 - x45) ≥ 1) ∧ ((x47 - x45) ≤ (t - 1)) ∧ ((x57 - x47) ≤ (t - 1))) ∨ ((x57 ≤ x47) ∧ (x47 ≤ x45) ∧ ((x45 - x57) ≥ 1) ∧ ((x45 - x47) ≤ (t - 1)) ∧ ((x47 - x57) ≤ (t - 1))))) : ((x45 ≤ x47) ∨ ((x47 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x45 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6455 (t x45 x47 x57 : ℝ) (h : (((x45 ≤ x47) ∧ (x47 ≤ x57) ∧ ((x57 - x45) ≥ 1) ∧ ((x47 - x45) ≤ (t - 1)) ∧ ((x57 - x47) ≤ (t - 1))) ∨ ((x57 ≤ x47) ∧ (x47 ≤ x45) ∧ ((x45 - x57) ≥ 1) ∧ ((x45 - x47) ≤ (t - 1)) ∧ ((x47 - x57) ≤ (t - 1))))) : ((x47 ≤ x57) ∨ (x57 ≤ x47)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x47 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x47) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6456 (t x45 x47 x57 : ℝ) (h : (((x45 ≤ x47) ∧ (x47 ≤ x57) ∧ ((x57 - x45) ≥ 1) ∧ ((x47 - x45) ≤ (t - 1)) ∧ ((x57 - x47) ≤ (t - 1))) ∨ ((x57 ≤ x47) ∧ (x47 ≤ x45) ∧ ((x45 - x57) ≥ 1) ∧ ((x45 - x47) ≤ (t - 1)) ∧ ((x47 - x57) ≤ (t - 1))))) : ((x47 ≤ x57) ∨ (x47 ≤ x45)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x47 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x45) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6457 (t x45 x47 x57 : ℝ) (h : (((x45 ≤ x47) ∧ (x47 ≤ x57) ∧ ((x57 - x45) ≥ 1) ∧ ((x47 - x45) ≤ (t - 1)) ∧ ((x57 - x47) ≤ (t - 1))) ∨ ((x57 ≤ x47) ∧ (x47 ≤ x45) ∧ ((x45 - x57) ≥ 1) ∧ ((x45 - x47) ≤ (t - 1)) ∧ ((x47 - x57) ≤ (t - 1))))) : ((x47 ≤ x57) ∨ ((x45 - x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x47 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x57) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6458 (t x45 x47 x57 : ℝ) (h : (((x45 ≤ x47) ∧ (x47 ≤ x57) ∧ ((x57 - x45) ≥ 1) ∧ ((x47 - x45) ≤ (t - 1)) ∧ ((x57 - x47) ≤ (t - 1))) ∨ ((x57 ≤ x47) ∧ (x47 ≤ x45) ∧ ((x45 - x57) ≥ 1) ∧ ((x45 - x47) ≤ (t - 1)) ∧ ((x47 - x57) ≤ (t - 1))))) : ((x47 ≤ x57) ∨ ((x45 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x47 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6459 (t x45 x47 x57 : ℝ) (h : (((x45 ≤ x47) ∧ (x47 ≤ x57) ∧ ((x57 - x45) ≥ 1) ∧ ((x47 - x45) ≤ (t - 1)) ∧ ((x57 - x47) ≤ (t - 1))) ∨ ((x57 ≤ x47) ∧ (x47 ≤ x45) ∧ ((x45 - x57) ≥ 1) ∧ ((x45 - x47) ≤ (t - 1)) ∧ ((x47 - x57) ≤ (t - 1))))) : ((x47 ≤ x57) ∨ ((x47 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x47 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6460 (t x45 x47 x57 : ℝ) (h : (((x45 ≤ x47) ∧ (x47 ≤ x57) ∧ ((x57 - x45) ≥ 1) ∧ ((x47 - x45) ≤ (t - 1)) ∧ ((x57 - x47) ≤ (t - 1))) ∨ ((x57 ≤ x47) ∧ (x47 ≤ x45) ∧ ((x45 - x57) ≥ 1) ∧ ((x45 - x47) ≤ (t - 1)) ∧ ((x47 - x57) ≤ (t - 1))))) : (((x57 - x45) ≥ 1) ∨ (x57 ≤ x47)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x45) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x47) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6461 (t x45 x47 x57 : ℝ) (h : (((x45 ≤ x47) ∧ (x47 ≤ x57) ∧ ((x57 - x45) ≥ 1) ∧ ((x47 - x45) ≤ (t - 1)) ∧ ((x57 - x47) ≤ (t - 1))) ∨ ((x57 ≤ x47) ∧ (x47 ≤ x45) ∧ ((x45 - x57) ≥ 1) ∧ ((x45 - x47) ≤ (t - 1)) ∧ ((x47 - x57) ≤ (t - 1))))) : (((x57 - x45) ≥ 1) ∨ (x47 ≤ x45)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x45) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x45) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6462 (t x45 x47 x57 : ℝ) (h : (((x45 ≤ x47) ∧ (x47 ≤ x57) ∧ ((x57 - x45) ≥ 1) ∧ ((x47 - x45) ≤ (t - 1)) ∧ ((x57 - x47) ≤ (t - 1))) ∨ ((x57 ≤ x47) ∧ (x47 ≤ x45) ∧ ((x45 - x57) ≥ 1) ∧ ((x45 - x47) ≤ (t - 1)) ∧ ((x47 - x57) ≤ (t - 1))))) : (((x57 - x45) ≥ 1) ∨ ((x45 - x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x45) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x57) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6463 (t x45 x47 x57 : ℝ) (h : (((x45 ≤ x47) ∧ (x47 ≤ x57) ∧ ((x57 - x45) ≥ 1) ∧ ((x47 - x45) ≤ (t - 1)) ∧ ((x57 - x47) ≤ (t - 1))) ∨ ((x57 ≤ x47) ∧ (x47 ≤ x45) ∧ ((x45 - x57) ≥ 1) ∧ ((x45 - x47) ≤ (t - 1)) ∧ ((x47 - x57) ≤ (t - 1))))) : (((x57 - x45) ≥ 1) ∨ ((x45 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x45) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6464 (t x45 x47 x57 : ℝ) (h : (((x45 ≤ x47) ∧ (x47 ≤ x57) ∧ ((x57 - x45) ≥ 1) ∧ ((x47 - x45) ≤ (t - 1)) ∧ ((x57 - x47) ≤ (t - 1))) ∨ ((x57 ≤ x47) ∧ (x47 ≤ x45) ∧ ((x45 - x57) ≥ 1) ∧ ((x45 - x47) ≤ (t - 1)) ∧ ((x47 - x57) ≤ (t - 1))))) : (((x57 - x45) ≥ 1) ∨ ((x47 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x45) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6465 (t x45 x47 x57 : ℝ) (h : (((x45 ≤ x47) ∧ (x47 ≤ x57) ∧ ((x57 - x45) ≥ 1) ∧ ((x47 - x45) ≤ (t - 1)) ∧ ((x57 - x47) ≤ (t - 1))) ∨ ((x57 ≤ x47) ∧ (x47 ≤ x45) ∧ ((x45 - x57) ≥ 1) ∧ ((x45 - x47) ≤ (t - 1)) ∧ ((x47 - x57) ≤ (t - 1))))) : (((x47 - x45) ≤ (t - 1)) ∨ (x57 ≤ x47)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x45) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x47) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6466 (t x45 x47 x57 : ℝ) (h : (((x45 ≤ x47) ∧ (x47 ≤ x57) ∧ ((x57 - x45) ≥ 1) ∧ ((x47 - x45) ≤ (t - 1)) ∧ ((x57 - x47) ≤ (t - 1))) ∨ ((x57 ≤ x47) ∧ (x47 ≤ x45) ∧ ((x45 - x57) ≥ 1) ∧ ((x45 - x47) ≤ (t - 1)) ∧ ((x47 - x57) ≤ (t - 1))))) : (((x47 - x45) ≤ (t - 1)) ∨ (x47 ≤ x45)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x45) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x45) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6467 (t x45 x47 x57 : ℝ) (h : (((x45 ≤ x47) ∧ (x47 ≤ x57) ∧ ((x57 - x45) ≥ 1) ∧ ((x47 - x45) ≤ (t - 1)) ∧ ((x57 - x47) ≤ (t - 1))) ∨ ((x57 ≤ x47) ∧ (x47 ≤ x45) ∧ ((x45 - x57) ≥ 1) ∧ ((x45 - x47) ≤ (t - 1)) ∧ ((x47 - x57) ≤ (t - 1))))) : (((x47 - x45) ≤ (t - 1)) ∨ ((x45 - x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x45) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x57) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6468 (t x45 x47 x57 : ℝ) (h : (((x45 ≤ x47) ∧ (x47 ≤ x57) ∧ ((x57 - x45) ≥ 1) ∧ ((x47 - x45) ≤ (t - 1)) ∧ ((x57 - x47) ≤ (t - 1))) ∨ ((x57 ≤ x47) ∧ (x47 ≤ x45) ∧ ((x45 - x57) ≥ 1) ∧ ((x45 - x47) ≤ (t - 1)) ∧ ((x47 - x57) ≤ (t - 1))))) : (((x47 - x45) ≤ (t - 1)) ∨ ((x45 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x45) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6469 (t x45 x47 x57 : ℝ) (h : (((x45 ≤ x47) ∧ (x47 ≤ x57) ∧ ((x57 - x45) ≥ 1) ∧ ((x47 - x45) ≤ (t - 1)) ∧ ((x57 - x47) ≤ (t - 1))) ∨ ((x57 ≤ x47) ∧ (x47 ≤ x45) ∧ ((x45 - x57) ≥ 1) ∧ ((x45 - x47) ≤ (t - 1)) ∧ ((x47 - x57) ≤ (t - 1))))) : (((x47 - x45) ≤ (t - 1)) ∨ ((x47 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x45) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6470 (t x45 x47 x57 : ℝ) (h : (((x45 ≤ x47) ∧ (x47 ≤ x57) ∧ ((x57 - x45) ≥ 1) ∧ ((x47 - x45) ≤ (t - 1)) ∧ ((x57 - x47) ≤ (t - 1))) ∨ ((x57 ≤ x47) ∧ (x47 ≤ x45) ∧ ((x45 - x57) ≥ 1) ∧ ((x45 - x47) ≤ (t - 1)) ∧ ((x47 - x57) ≤ (t - 1))))) : (((x57 - x47) ≤ (t - 1)) ∨ (x57 ≤ x47)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x47) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x47) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6471 (t x45 x47 x57 : ℝ) (h : (((x45 ≤ x47) ∧ (x47 ≤ x57) ∧ ((x57 - x45) ≥ 1) ∧ ((x47 - x45) ≤ (t - 1)) ∧ ((x57 - x47) ≤ (t - 1))) ∨ ((x57 ≤ x47) ∧ (x47 ≤ x45) ∧ ((x45 - x57) ≥ 1) ∧ ((x45 - x47) ≤ (t - 1)) ∧ ((x47 - x57) ≤ (t - 1))))) : (((x57 - x47) ≤ (t - 1)) ∨ (x47 ≤ x45)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x47) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x45) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6472 (t x45 x47 x57 : ℝ) (h : (((x45 ≤ x47) ∧ (x47 ≤ x57) ∧ ((x57 - x45) ≥ 1) ∧ ((x47 - x45) ≤ (t - 1)) ∧ ((x57 - x47) ≤ (t - 1))) ∨ ((x57 ≤ x47) ∧ (x47 ≤ x45) ∧ ((x45 - x57) ≥ 1) ∧ ((x45 - x47) ≤ (t - 1)) ∧ ((x47 - x57) ≤ (t - 1))))) : (((x57 - x47) ≤ (t - 1)) ∨ ((x45 - x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x47) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x57) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6473 (t x45 x47 x57 : ℝ) (h : (((x45 ≤ x47) ∧ (x47 ≤ x57) ∧ ((x57 - x45) ≥ 1) ∧ ((x47 - x45) ≤ (t - 1)) ∧ ((x57 - x47) ≤ (t - 1))) ∨ ((x57 ≤ x47) ∧ (x47 ≤ x45) ∧ ((x45 - x57) ≥ 1) ∧ ((x45 - x47) ≤ (t - 1)) ∧ ((x47 - x57) ≤ (t - 1))))) : (((x57 - x47) ≤ (t - 1)) ∨ ((x45 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x47) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6474 (t x45 x47 x57 : ℝ) (h : (((x45 ≤ x47) ∧ (x47 ≤ x57) ∧ ((x57 - x45) ≥ 1) ∧ ((x47 - x45) ≤ (t - 1)) ∧ ((x57 - x47) ≤ (t - 1))) ∨ ((x57 ≤ x47) ∧ (x47 ≤ x45) ∧ ((x45 - x57) ≥ 1) ∧ ((x45 - x47) ≤ (t - 1)) ∧ ((x47 - x57) ≤ (t - 1))))) : (((x57 - x47) ≤ (t - 1)) ∨ ((x47 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x47) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6475 (t x04 x14 x15 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + x04 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x15)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x04 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th366 t x04 x14 x15 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u5 u3))))))) h

theorem clause6476 (x15 x45 x57 : ℝ) : ((¬ ((x15 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1))) := by
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
  have u2 : ((x15 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th367 x15 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 u2)))) h

theorem clause6477 (t x01 x13 x15 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x13)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th368 t x01 x13 x15 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u5 (And.intro u0 (And.intro u4 (And.intro u2 u6)))))))) h

theorem clause6478 (x45 : ℝ) (h : (x45 ≥ 0)) : ((x45 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x45 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause6481 (t x01 x05 x15 : ℝ) : (((x01 + ((-1) * x15)) ≥ 1) ∨ ((x01 + ((-1) * x05)) ≤ 0) ∨ (¬ (x01 ≤ x05)) ∨ (¬ (x05 ≤ x15)) ∨ (¬ ((x15 - x01) ≥ 1)) ∨ (¬ ((x05 - x01) ≤ (t - 1))) ∨ (¬ ((x15 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x15)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x05)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th371 t x01 x05 x15
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6486 (t x01 x05 x15 : ℝ) : (((x01 + ((-1) * x15)) ≥ 1) ∨ ((x05 + ((-1) * x15)) ≤ 0) ∨ (¬ (x01 ≤ x05)) ∨ (¬ (x05 ≤ x15)) ∨ (¬ ((x15 - x01) ≥ 1)) ∨ (¬ ((x05 - x01) ≤ (t - 1))) ∨ (¬ ((x15 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x15)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x15)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th371 t x01 x05 x15
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6488 (t x01 x05 x15 : ℝ) : (((x05 + ((-1) * x15)) ≤ 0) ∨ ((t + ((-1) * x05) + x15) ≥ 1) ∨ (¬ (x01 ≤ x05)) ∨ (¬ (x05 ≤ x15)) ∨ (¬ ((x15 - x01) ≥ 1)) ∨ (¬ ((x05 - x01) ≤ (t - 1))) ∨ (¬ ((x15 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x15)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x05) + x15) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th371 t x01 x05 x15
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6489 (t x01 x05 x15 : ℝ) : (((x01 + ((-1) * x15)) ≤ (-1)) ∨ ((x05 + ((-1) * x15)) ≥ 0) ∨ (¬ (x01 ≤ x05)) ∨ (¬ (x05 ≤ x15)) ∨ (¬ ((x15 - x01) ≥ 1)) ∨ (¬ ((x05 - x01) ≤ (t - 1))) ∨ (¬ ((x15 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x15)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x15)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th371 t x01 x05 x15
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6490 (t x01 x05 x15 : ℝ) : (((x01 + ((-1) * x05)) ≥ 0) ∨ ((x01 + ((-1) * x15)) ≤ (-1)) ∨ (¬ (x01 ≤ x05)) ∨ (¬ (x05 ≤ x15)) ∨ (¬ ((x15 - x01) ≥ 1)) ∨ (¬ ((x05 - x01) ≤ (t - 1))) ∨ (¬ ((x15 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x05)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x15)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th371 t x01 x05 x15
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6491 (t x01 x05 x15 : ℝ) : (((x01 + ((-1) * x15)) ≥ 1) ∨ ((x01 + ((-1) * x15)) ≤ (-1)) ∨ (¬ (x01 ≤ x05)) ∨ (¬ (x05 ≤ x15)) ∨ (¬ ((x15 - x01) ≥ 1)) ∨ (¬ ((x05 - x01) ≤ (t - 1))) ∨ (¬ ((x15 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x15)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x15)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th371 t x01 x05 x15
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6492 (t x01 x05 x15 : ℝ) : (((x01 + ((-1) * x15)) ≤ (-1)) ∨ ((t + ((-1) * x01) + x05) ≥ 1) ∨ (¬ (x01 ≤ x05)) ∨ (¬ (x05 ≤ x15)) ∨ (¬ ((x15 - x01) ≥ 1)) ∨ (¬ ((x05 - x01) ≤ (t - 1))) ∨ (¬ ((x15 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x15)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x01) + x05) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th371 t x01 x05 x15
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6496 (t x01 x05 x15 : ℝ) : (((x01 + ((-1) * x15)) ≥ 1) ∨ ((t + x01 + ((-1) * x05)) ≥ 1) ∨ (¬ (x01 ≤ x05)) ∨ (¬ (x05 ≤ x15)) ∨ (¬ ((x15 - x01) ≥ 1)) ∨ (¬ ((x05 - x01) ≤ (t - 1))) ∨ (¬ ((x15 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x15)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x01 + ((-1) * x05)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th371 t x01 x05 x15
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6499 (t x01 x05 x15 : ℝ) : (((t + x05 + ((-1) * x15)) ≥ 1) ∨ ((x05 + ((-1) * x15)) ≥ 0) ∨ (¬ (x01 ≤ x05)) ∨ (¬ (x05 ≤ x15)) ∨ (¬ ((x15 - x01) ≥ 1)) ∨ (¬ ((x05 - x01) ≤ (t - 1))) ∨ (¬ ((x15 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x05 + ((-1) * x15)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x15)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th371 t x01 x05 x15
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6501 (t x01 x05 x15 : ℝ) : (((x01 + ((-1) * x15)) ≥ 1) ∨ ((t + x05 + ((-1) * x15)) ≥ 1) ∨ (¬ (x01 ≤ x05)) ∨ (¬ (x05 ≤ x15)) ∨ (¬ ((x15 - x01) ≥ 1)) ∨ (¬ ((x05 - x01) ≤ (t - 1))) ∨ (¬ ((x15 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x15)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x05 + ((-1) * x15)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th371 t x01 x05 x15
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6506 (t x01 x05 x15 : ℝ) : (((x01 + ((-1) * x15)) ≥ 1) ∨ ((x01 + ((-1) * x05)) ≤ 0) ∨ (¬ (x15 ≤ x05)) ∨ (¬ (x05 ≤ x01)) ∨ (¬ ((x01 - x15) ≥ 1)) ∨ (¬ ((x01 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x15)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x05)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th371 t x01 x05 x15
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6511 (t x01 x05 x15 : ℝ) : (((x01 + ((-1) * x15)) ≥ 1) ∨ ((x05 + ((-1) * x15)) ≤ 0) ∨ (¬ (x15 ≤ x05)) ∨ (¬ (x05 ≤ x01)) ∨ (¬ ((x01 - x15) ≥ 1)) ∨ (¬ ((x01 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x15)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x15)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th371 t x01 x05 x15
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6513 (t x01 x05 x15 : ℝ) : (((x05 + ((-1) * x15)) ≤ 0) ∨ ((t + ((-1) * x05) + x15) ≥ 1) ∨ (¬ (x15 ≤ x05)) ∨ (¬ (x05 ≤ x01)) ∨ (¬ ((x01 - x15) ≥ 1)) ∨ (¬ ((x01 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x15)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x05) + x15) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th371 t x01 x05 x15
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6514 (t x01 x05 x15 : ℝ) : (((x01 + ((-1) * x15)) ≤ (-1)) ∨ ((x05 + ((-1) * x15)) ≥ 0) ∨ (¬ (x15 ≤ x05)) ∨ (¬ (x05 ≤ x01)) ∨ (¬ ((x01 - x15) ≥ 1)) ∨ (¬ ((x01 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x15)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x15)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th371 t x01 x05 x15
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6515 (t x01 x05 x15 : ℝ) : (((x01 + ((-1) * x05)) ≥ 0) ∨ ((x01 + ((-1) * x15)) ≤ (-1)) ∨ (¬ (x15 ≤ x05)) ∨ (¬ (x05 ≤ x01)) ∨ (¬ ((x01 - x15) ≥ 1)) ∨ (¬ ((x01 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x05)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x15)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th371 t x01 x05 x15
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6516 (t x01 x05 x15 : ℝ) : (((x01 + ((-1) * x15)) ≥ 1) ∨ ((x01 + ((-1) * x15)) ≤ (-1)) ∨ (¬ (x15 ≤ x05)) ∨ (¬ (x05 ≤ x01)) ∨ (¬ ((x01 - x15) ≥ 1)) ∨ (¬ ((x01 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x15)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x15)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th371 t x01 x05 x15
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6517 (t x01 x05 x15 : ℝ) : (((x01 + ((-1) * x15)) ≤ (-1)) ∨ ((t + ((-1) * x01) + x05) ≥ 1) ∨ (¬ (x15 ≤ x05)) ∨ (¬ (x05 ≤ x01)) ∨ (¬ ((x01 - x15) ≥ 1)) ∨ (¬ ((x01 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x15)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x01) + x05) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th371 t x01 x05 x15
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6521 (t x01 x05 x15 : ℝ) : (((x01 + ((-1) * x15)) ≥ 1) ∨ ((t + x01 + ((-1) * x05)) ≥ 1) ∨ (¬ (x15 ≤ x05)) ∨ (¬ (x05 ≤ x01)) ∨ (¬ ((x01 - x15) ≥ 1)) ∨ (¬ ((x01 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x15)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x01 + ((-1) * x05)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th371 t x01 x05 x15
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6526 (t x01 x05 x15 : ℝ) : (((x01 + ((-1) * x15)) ≥ 1) ∨ ((t + x05 + ((-1) * x15)) ≥ 1) ∨ (¬ (x15 ≤ x05)) ∨ (¬ (x05 ≤ x01)) ∨ (¬ ((x01 - x15) ≥ 1)) ∨ (¬ ((x01 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x15)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x05 + ((-1) * x15)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th371 t x01 x05 x15
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6579 (t x01 x05 x15 : ℝ) (h : (((x01 ≤ x05) ∧ (x05 ≤ x15) ∧ ((x15 - x01) ≥ 1) ∧ ((x05 - x01) ≤ (t - 1)) ∧ ((x15 - x05) ≤ (t - 1))) ∨ ((x15 ≤ x05) ∧ (x05 ≤ x01) ∧ ((x01 - x15) ≥ 1) ∧ ((x01 - x05) ≤ (t - 1)) ∧ ((x05 - x15) ≤ (t - 1))))) : ((x01 ≤ x05) ∨ (x15 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x05) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x15 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6580 (t x01 x05 x15 : ℝ) (h : (((x01 ≤ x05) ∧ (x05 ≤ x15) ∧ ((x15 - x01) ≥ 1) ∧ ((x05 - x01) ≤ (t - 1)) ∧ ((x15 - x05) ≤ (t - 1))) ∨ ((x15 ≤ x05) ∧ (x05 ≤ x01) ∧ ((x01 - x15) ≥ 1) ∧ ((x01 - x05) ≤ (t - 1)) ∧ ((x05 - x15) ≤ (t - 1))))) : ((x01 ≤ x05) ∨ (x05 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x05) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x05 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6581 (t x01 x05 x15 : ℝ) (h : (((x01 ≤ x05) ∧ (x05 ≤ x15) ∧ ((x15 - x01) ≥ 1) ∧ ((x05 - x01) ≤ (t - 1)) ∧ ((x15 - x05) ≤ (t - 1))) ∨ ((x15 ≤ x05) ∧ (x05 ≤ x01) ∧ ((x01 - x15) ≥ 1) ∧ ((x01 - x05) ≤ (t - 1)) ∧ ((x05 - x15) ≤ (t - 1))))) : ((x01 ≤ x05) ∨ ((x01 - x15) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x05) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x15) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6582 (t x01 x05 x15 : ℝ) (h : (((x01 ≤ x05) ∧ (x05 ≤ x15) ∧ ((x15 - x01) ≥ 1) ∧ ((x05 - x01) ≤ (t - 1)) ∧ ((x15 - x05) ≤ (t - 1))) ∨ ((x15 ≤ x05) ∧ (x05 ≤ x01) ∧ ((x01 - x15) ≥ 1) ∧ ((x01 - x05) ≤ (t - 1)) ∧ ((x05 - x15) ≤ (t - 1))))) : ((x01 ≤ x05) ∨ ((x01 - x05) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x05) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x05) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6583 (t x01 x05 x15 : ℝ) (h : (((x01 ≤ x05) ∧ (x05 ≤ x15) ∧ ((x15 - x01) ≥ 1) ∧ ((x05 - x01) ≤ (t - 1)) ∧ ((x15 - x05) ≤ (t - 1))) ∨ ((x15 ≤ x05) ∧ (x05 ≤ x01) ∧ ((x01 - x15) ≥ 1) ∧ ((x01 - x05) ≤ (t - 1)) ∧ ((x05 - x15) ≤ (t - 1))))) : ((x01 ≤ x05) ∨ ((x05 - x15) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x05) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x15) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6584 (t x01 x05 x15 : ℝ) (h : (((x01 ≤ x05) ∧ (x05 ≤ x15) ∧ ((x15 - x01) ≥ 1) ∧ ((x05 - x01) ≤ (t - 1)) ∧ ((x15 - x05) ≤ (t - 1))) ∨ ((x15 ≤ x05) ∧ (x05 ≤ x01) ∧ ((x01 - x15) ≥ 1) ∧ ((x01 - x05) ≤ (t - 1)) ∧ ((x05 - x15) ≤ (t - 1))))) : ((x05 ≤ x15) ∨ (x15 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x15) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x15 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6585 (t x01 x05 x15 : ℝ) (h : (((x01 ≤ x05) ∧ (x05 ≤ x15) ∧ ((x15 - x01) ≥ 1) ∧ ((x05 - x01) ≤ (t - 1)) ∧ ((x15 - x05) ≤ (t - 1))) ∨ ((x15 ≤ x05) ∧ (x05 ≤ x01) ∧ ((x01 - x15) ≥ 1) ∧ ((x01 - x05) ≤ (t - 1)) ∧ ((x05 - x15) ≤ (t - 1))))) : ((x05 ≤ x15) ∨ (x05 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x15) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x05 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6586 (t x01 x05 x15 : ℝ) (h : (((x01 ≤ x05) ∧ (x05 ≤ x15) ∧ ((x15 - x01) ≥ 1) ∧ ((x05 - x01) ≤ (t - 1)) ∧ ((x15 - x05) ≤ (t - 1))) ∨ ((x15 ≤ x05) ∧ (x05 ≤ x01) ∧ ((x01 - x15) ≥ 1) ∧ ((x01 - x05) ≤ (t - 1)) ∧ ((x05 - x15) ≤ (t - 1))))) : ((x05 ≤ x15) ∨ ((x01 - x15) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x15) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x15) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6587 (t x01 x05 x15 : ℝ) (h : (((x01 ≤ x05) ∧ (x05 ≤ x15) ∧ ((x15 - x01) ≥ 1) ∧ ((x05 - x01) ≤ (t - 1)) ∧ ((x15 - x05) ≤ (t - 1))) ∨ ((x15 ≤ x05) ∧ (x05 ≤ x01) ∧ ((x01 - x15) ≥ 1) ∧ ((x01 - x05) ≤ (t - 1)) ∧ ((x05 - x15) ≤ (t - 1))))) : ((x05 ≤ x15) ∨ ((x01 - x05) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x15) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x05) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6588 (t x01 x05 x15 : ℝ) (h : (((x01 ≤ x05) ∧ (x05 ≤ x15) ∧ ((x15 - x01) ≥ 1) ∧ ((x05 - x01) ≤ (t - 1)) ∧ ((x15 - x05) ≤ (t - 1))) ∨ ((x15 ≤ x05) ∧ (x05 ≤ x01) ∧ ((x01 - x15) ≥ 1) ∧ ((x01 - x05) ≤ (t - 1)) ∧ ((x05 - x15) ≤ (t - 1))))) : ((x05 ≤ x15) ∨ ((x05 - x15) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x15) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x15) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6589 (t x01 x05 x15 : ℝ) (h : (((x01 ≤ x05) ∧ (x05 ≤ x15) ∧ ((x15 - x01) ≥ 1) ∧ ((x05 - x01) ≤ (t - 1)) ∧ ((x15 - x05) ≤ (t - 1))) ∨ ((x15 ≤ x05) ∧ (x05 ≤ x01) ∧ ((x01 - x15) ≥ 1) ∧ ((x01 - x05) ≤ (t - 1)) ∧ ((x05 - x15) ≤ (t - 1))))) : (((x15 - x01) ≥ 1) ∨ (x15 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x15 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6590 (t x01 x05 x15 : ℝ) (h : (((x01 ≤ x05) ∧ (x05 ≤ x15) ∧ ((x15 - x01) ≥ 1) ∧ ((x05 - x01) ≤ (t - 1)) ∧ ((x15 - x05) ≤ (t - 1))) ∨ ((x15 ≤ x05) ∧ (x05 ≤ x01) ∧ ((x01 - x15) ≥ 1) ∧ ((x01 - x05) ≤ (t - 1)) ∧ ((x05 - x15) ≤ (t - 1))))) : (((x15 - x01) ≥ 1) ∨ (x05 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x05 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6591 (t x01 x05 x15 : ℝ) (h : (((x01 ≤ x05) ∧ (x05 ≤ x15) ∧ ((x15 - x01) ≥ 1) ∧ ((x05 - x01) ≤ (t - 1)) ∧ ((x15 - x05) ≤ (t - 1))) ∨ ((x15 ≤ x05) ∧ (x05 ≤ x01) ∧ ((x01 - x15) ≥ 1) ∧ ((x01 - x05) ≤ (t - 1)) ∧ ((x05 - x15) ≤ (t - 1))))) : (((x15 - x01) ≥ 1) ∨ ((x01 - x15) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x15) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6592 (t x01 x05 x15 : ℝ) (h : (((x01 ≤ x05) ∧ (x05 ≤ x15) ∧ ((x15 - x01) ≥ 1) ∧ ((x05 - x01) ≤ (t - 1)) ∧ ((x15 - x05) ≤ (t - 1))) ∨ ((x15 ≤ x05) ∧ (x05 ≤ x01) ∧ ((x01 - x15) ≥ 1) ∧ ((x01 - x05) ≤ (t - 1)) ∧ ((x05 - x15) ≤ (t - 1))))) : (((x15 - x01) ≥ 1) ∨ ((x01 - x05) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x05) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6593 (t x01 x05 x15 : ℝ) (h : (((x01 ≤ x05) ∧ (x05 ≤ x15) ∧ ((x15 - x01) ≥ 1) ∧ ((x05 - x01) ≤ (t - 1)) ∧ ((x15 - x05) ≤ (t - 1))) ∨ ((x15 ≤ x05) ∧ (x05 ≤ x01) ∧ ((x01 - x15) ≥ 1) ∧ ((x01 - x05) ≤ (t - 1)) ∧ ((x05 - x15) ≤ (t - 1))))) : (((x15 - x01) ≥ 1) ∨ ((x05 - x15) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x15) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6594 (t x01 x05 x15 : ℝ) (h : (((x01 ≤ x05) ∧ (x05 ≤ x15) ∧ ((x15 - x01) ≥ 1) ∧ ((x05 - x01) ≤ (t - 1)) ∧ ((x15 - x05) ≤ (t - 1))) ∨ ((x15 ≤ x05) ∧ (x05 ≤ x01) ∧ ((x01 - x15) ≥ 1) ∧ ((x01 - x05) ≤ (t - 1)) ∧ ((x05 - x15) ≤ (t - 1))))) : (((x05 - x01) ≤ (t - 1)) ∨ (x15 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x15 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6595 (t x01 x05 x15 : ℝ) (h : (((x01 ≤ x05) ∧ (x05 ≤ x15) ∧ ((x15 - x01) ≥ 1) ∧ ((x05 - x01) ≤ (t - 1)) ∧ ((x15 - x05) ≤ (t - 1))) ∨ ((x15 ≤ x05) ∧ (x05 ≤ x01) ∧ ((x01 - x15) ≥ 1) ∧ ((x01 - x05) ≤ (t - 1)) ∧ ((x05 - x15) ≤ (t - 1))))) : (((x05 - x01) ≤ (t - 1)) ∨ (x05 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x05 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6596 (t x01 x05 x15 : ℝ) (h : (((x01 ≤ x05) ∧ (x05 ≤ x15) ∧ ((x15 - x01) ≥ 1) ∧ ((x05 - x01) ≤ (t - 1)) ∧ ((x15 - x05) ≤ (t - 1))) ∨ ((x15 ≤ x05) ∧ (x05 ≤ x01) ∧ ((x01 - x15) ≥ 1) ∧ ((x01 - x05) ≤ (t - 1)) ∧ ((x05 - x15) ≤ (t - 1))))) : (((x05 - x01) ≤ (t - 1)) ∨ ((x01 - x15) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x15) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6597 (t x01 x05 x15 : ℝ) (h : (((x01 ≤ x05) ∧ (x05 ≤ x15) ∧ ((x15 - x01) ≥ 1) ∧ ((x05 - x01) ≤ (t - 1)) ∧ ((x15 - x05) ≤ (t - 1))) ∨ ((x15 ≤ x05) ∧ (x05 ≤ x01) ∧ ((x01 - x15) ≥ 1) ∧ ((x01 - x05) ≤ (t - 1)) ∧ ((x05 - x15) ≤ (t - 1))))) : (((x05 - x01) ≤ (t - 1)) ∨ ((x01 - x05) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x05) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6598 (t x01 x05 x15 : ℝ) (h : (((x01 ≤ x05) ∧ (x05 ≤ x15) ∧ ((x15 - x01) ≥ 1) ∧ ((x05 - x01) ≤ (t - 1)) ∧ ((x15 - x05) ≤ (t - 1))) ∨ ((x15 ≤ x05) ∧ (x05 ≤ x01) ∧ ((x01 - x15) ≥ 1) ∧ ((x01 - x05) ≤ (t - 1)) ∧ ((x05 - x15) ≤ (t - 1))))) : (((x05 - x01) ≤ (t - 1)) ∨ ((x05 - x15) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x15) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6599 (t x01 x05 x15 : ℝ) (h : (((x01 ≤ x05) ∧ (x05 ≤ x15) ∧ ((x15 - x01) ≥ 1) ∧ ((x05 - x01) ≤ (t - 1)) ∧ ((x15 - x05) ≤ (t - 1))) ∨ ((x15 ≤ x05) ∧ (x05 ≤ x01) ∧ ((x01 - x15) ≥ 1) ∧ ((x01 - x05) ≤ (t - 1)) ∧ ((x05 - x15) ≤ (t - 1))))) : (((x15 - x05) ≤ (t - 1)) ∨ (x15 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x15 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6600 (t x01 x05 x15 : ℝ) (h : (((x01 ≤ x05) ∧ (x05 ≤ x15) ∧ ((x15 - x01) ≥ 1) ∧ ((x05 - x01) ≤ (t - 1)) ∧ ((x15 - x05) ≤ (t - 1))) ∨ ((x15 ≤ x05) ∧ (x05 ≤ x01) ∧ ((x01 - x15) ≥ 1) ∧ ((x01 - x05) ≤ (t - 1)) ∧ ((x05 - x15) ≤ (t - 1))))) : (((x15 - x05) ≤ (t - 1)) ∨ (x05 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x05 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6601 (t x01 x05 x15 : ℝ) (h : (((x01 ≤ x05) ∧ (x05 ≤ x15) ∧ ((x15 - x01) ≥ 1) ∧ ((x05 - x01) ≤ (t - 1)) ∧ ((x15 - x05) ≤ (t - 1))) ∨ ((x15 ≤ x05) ∧ (x05 ≤ x01) ∧ ((x01 - x15) ≥ 1) ∧ ((x01 - x05) ≤ (t - 1)) ∧ ((x05 - x15) ≤ (t - 1))))) : (((x15 - x05) ≤ (t - 1)) ∨ ((x01 - x15) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x15) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6602 (t x01 x05 x15 : ℝ) (h : (((x01 ≤ x05) ∧ (x05 ≤ x15) ∧ ((x15 - x01) ≥ 1) ∧ ((x05 - x01) ≤ (t - 1)) ∧ ((x15 - x05) ≤ (t - 1))) ∨ ((x15 ≤ x05) ∧ (x05 ≤ x01) ∧ ((x01 - x15) ≥ 1) ∧ ((x01 - x05) ≤ (t - 1)) ∧ ((x05 - x15) ≤ (t - 1))))) : (((x15 - x05) ≤ (t - 1)) ∨ ((x01 - x05) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x05) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6603 (t x01 x05 x15 : ℝ) (h : (((x01 ≤ x05) ∧ (x05 ≤ x15) ∧ ((x15 - x01) ≥ 1) ∧ ((x05 - x01) ≤ (t - 1)) ∧ ((x15 - x05) ≤ (t - 1))) ∨ ((x15 ≤ x05) ∧ (x05 ≤ x01) ∧ ((x01 - x15) ≥ 1) ∧ ((x01 - x05) ≤ (t - 1)) ∧ ((x05 - x15) ≤ (t - 1))))) : (((x15 - x05) ≤ (t - 1)) ∨ ((x05 - x15) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x15) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6604 (x01 x13 : ℝ) : ((¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th374 x01 x13
  exact (fun hh => (Or.elim hh (fun hh => hh u1) (fun zz => ((fun hh => hh u0) zz)))) h

theorem clause6605 (t x04 x05 x45 x46 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((t + x45 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x45 + ((-1) * x46)) ≥ 1) := by
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
  have h := NineTheoryTrial.th375 t x04 x05 x45 x46 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u4 (And.intro u0 (And.intro u5 u3))))))) h

theorem clause6606 (t x12 x15 x23 x25 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x23) + x25) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x15)) ≥ 0)) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x23) + x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th377 t x12 x15 x23 x25 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u2 u5))))))) h

theorem clause6607 (t x12 x23 x25 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x45 ≥ 0) := by
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
  have h := NineTheoryTrial.th378 t x12 x23 x25 x45 x57
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u4 u3))))))) h

theorem clause6608 (t x25 x27 x57 : ℝ) : (((x25 + ((-1) * x27)) ≤ 0) ∨ ((x27 + ((-1) * x57)) ≥ 0) ∨ (¬ (x25 ≤ x27)) ∨ (¬ (x27 ≤ x57)) ∨ (¬ ((x57 - x25) ≥ 1)) ∨ (¬ ((x27 - x25) ≤ (t - 1))) ∨ (¬ ((x57 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x57)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th380 t x25 x27 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6610 (t x25 x27 x57 : ℝ) : (((x25 + ((-1) * x57)) ≥ 1) ∨ ((x25 + ((-1) * x27)) ≤ 0) ∨ (¬ (x25 ≤ x27)) ∨ (¬ (x27 ≤ x57)) ∨ (¬ ((x57 - x25) ≥ 1)) ∨ (¬ ((x27 - x25) ≤ (t - 1))) ∨ (¬ ((x57 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th380 t x25 x27 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6614 (t x25 x27 x57 : ℝ) : (((x27 + ((-1) * x57)) ≤ 0) ∨ ((x25 + ((-1) * x27)) ≥ 0) ∨ (¬ (x25 ≤ x27)) ∨ (¬ (x27 ≤ x57)) ∨ (¬ ((x57 - x25) ≥ 1)) ∨ (¬ ((x27 - x25) ≤ (t - 1))) ∨ (¬ ((x57 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x27)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th380 t x25 x27 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6615 (t x25 x27 x57 : ℝ) : (((x25 + ((-1) * x57)) ≥ 1) ∨ ((x27 + ((-1) * x57)) ≤ 0) ∨ (¬ (x25 ≤ x27)) ∨ (¬ (x27 ≤ x57)) ∨ (¬ ((x57 - x25) ≥ 1)) ∨ (¬ ((x27 - x25) ≤ (t - 1))) ∨ (¬ ((x57 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th380 t x25 x27 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6617 (t x25 x27 x57 : ℝ) : (((x27 + ((-1) * x57)) ≤ 0) ∨ ((t + ((-1) * x27) + x57) ≥ 1) ∨ (¬ (x25 ≤ x27)) ∨ (¬ (x27 ≤ x57)) ∨ (¬ ((x57 - x25) ≥ 1)) ∨ (¬ ((x27 - x25) ≤ (t - 1))) ∨ (¬ ((x57 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x27) + x57) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th380 t x25 x27 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6618 (t x25 x27 x57 : ℝ) : (((x25 + ((-1) * x57)) ≤ (-1)) ∨ ((x27 + ((-1) * x57)) ≥ 0) ∨ (¬ (x25 ≤ x27)) ∨ (¬ (x27 ≤ x57)) ∨ (¬ ((x57 - x25) ≥ 1)) ∨ (¬ ((x27 - x25) ≤ (t - 1))) ∨ (¬ ((x57 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x57)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th380 t x25 x27 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6619 (t x25 x27 x57 : ℝ) : (((x25 + ((-1) * x57)) ≤ (-1)) ∨ ((x25 + ((-1) * x27)) ≥ 0) ∨ (¬ (x25 ≤ x27)) ∨ (¬ (x27 ≤ x57)) ∨ (¬ ((x57 - x25) ≥ 1)) ∨ (¬ ((x27 - x25) ≤ (t - 1))) ∨ (¬ ((x57 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x27)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th380 t x25 x27 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6620 (t x25 x27 x57 : ℝ) : (((x25 + ((-1) * x57)) ≤ (-1)) ∨ ((x25 + ((-1) * x57)) ≥ 1) ∨ (¬ (x25 ≤ x27)) ∨ (¬ (x27 ≤ x57)) ∨ (¬ ((x57 - x25) ≥ 1)) ∨ (¬ ((x27 - x25) ≤ (t - 1))) ∨ (¬ ((x57 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th380 t x25 x27 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6630 (t x25 x27 x57 : ℝ) : (((x25 + ((-1) * x57)) ≥ 1) ∨ ((t + x27 + ((-1) * x57)) ≥ 1) ∨ (¬ (x25 ≤ x27)) ∨ (¬ (x27 ≤ x57)) ∨ (¬ ((x57 - x25) ≥ 1)) ∨ (¬ ((x27 - x25) ≤ (t - 1))) ∨ (¬ ((x57 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x27 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th380 t x25 x27 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6633 (t x25 x27 x57 : ℝ) : (((x25 + ((-1) * x27)) ≤ 0) ∨ ((x27 + ((-1) * x57)) ≥ 0) ∨ (¬ (x57 ≤ x27)) ∨ (¬ (x27 ≤ x25)) ∨ (¬ ((x25 - x57) ≥ 1)) ∨ (¬ ((x25 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x57)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th380 t x25 x27 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6635 (t x25 x27 x57 : ℝ) : (((x25 + ((-1) * x57)) ≥ 1) ∨ ((x25 + ((-1) * x27)) ≤ 0) ∨ (¬ (x57 ≤ x27)) ∨ (¬ (x27 ≤ x25)) ∨ (¬ ((x25 - x57) ≥ 1)) ∨ (¬ ((x25 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th380 t x25 x27 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6639 (t x25 x27 x57 : ℝ) : (((x27 + ((-1) * x57)) ≤ 0) ∨ ((x25 + ((-1) * x27)) ≥ 0) ∨ (¬ (x57 ≤ x27)) ∨ (¬ (x27 ≤ x25)) ∨ (¬ ((x25 - x57) ≥ 1)) ∨ (¬ ((x25 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x27)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th380 t x25 x27 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6640 (t x25 x27 x57 : ℝ) : (((x25 + ((-1) * x57)) ≥ 1) ∨ ((x27 + ((-1) * x57)) ≤ 0) ∨ (¬ (x57 ≤ x27)) ∨ (¬ (x27 ≤ x25)) ∨ (¬ ((x25 - x57) ≥ 1)) ∨ (¬ ((x25 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th380 t x25 x27 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6642 (t x25 x27 x57 : ℝ) : (((x27 + ((-1) * x57)) ≤ 0) ∨ ((t + ((-1) * x27) + x57) ≥ 1) ∨ (¬ (x57 ≤ x27)) ∨ (¬ (x27 ≤ x25)) ∨ (¬ ((x25 - x57) ≥ 1)) ∨ (¬ ((x25 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x27) + x57) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th380 t x25 x27 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6643 (t x25 x27 x57 : ℝ) : (((x25 + ((-1) * x57)) ≤ (-1)) ∨ ((x27 + ((-1) * x57)) ≥ 0) ∨ (¬ (x57 ≤ x27)) ∨ (¬ (x27 ≤ x25)) ∨ (¬ ((x25 - x57) ≥ 1)) ∨ (¬ ((x25 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x57)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th380 t x25 x27 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6644 (t x25 x27 x57 : ℝ) : (((x25 + ((-1) * x57)) ≤ (-1)) ∨ ((x25 + ((-1) * x27)) ≥ 0) ∨ (¬ (x57 ≤ x27)) ∨ (¬ (x27 ≤ x25)) ∨ (¬ ((x25 - x57) ≥ 1)) ∨ (¬ ((x25 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x27)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th380 t x25 x27 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6645 (t x25 x27 x57 : ℝ) : (((x25 + ((-1) * x57)) ≤ (-1)) ∨ ((x25 + ((-1) * x57)) ≥ 1) ∨ (¬ (x57 ≤ x27)) ∨ (¬ (x27 ≤ x25)) ∨ (¬ ((x25 - x57) ≥ 1)) ∨ (¬ ((x25 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th380 t x25 x27 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6655 (t x25 x27 x57 : ℝ) : (((x25 + ((-1) * x57)) ≥ 1) ∨ ((t + x27 + ((-1) * x57)) ≥ 1) ∨ (¬ (x57 ≤ x27)) ∨ (¬ (x27 ≤ x25)) ∨ (¬ ((x25 - x57) ≥ 1)) ∨ (¬ ((x25 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x27 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th380 t x25 x27 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6708 (t x25 x27 x57 : ℝ) (h : (((x25 ≤ x27) ∧ (x27 ≤ x57) ∧ ((x57 - x25) ≥ 1) ∧ ((x27 - x25) ≤ (t - 1)) ∧ ((x57 - x27) ≤ (t - 1))) ∨ ((x57 ≤ x27) ∧ (x27 ≤ x25) ∧ ((x25 - x57) ≥ 1) ∧ ((x25 - x27) ≤ (t - 1)) ∧ ((x27 - x57) ≤ (t - 1))))) : ((x25 ≤ x27) ∨ (x57 ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x27) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6709 (t x25 x27 x57 : ℝ) (h : (((x25 ≤ x27) ∧ (x27 ≤ x57) ∧ ((x57 - x25) ≥ 1) ∧ ((x27 - x25) ≤ (t - 1)) ∧ ((x57 - x27) ≤ (t - 1))) ∨ ((x57 ≤ x27) ∧ (x27 ≤ x25) ∧ ((x25 - x57) ≥ 1) ∧ ((x25 - x27) ≤ (t - 1)) ∧ ((x27 - x57) ≤ (t - 1))))) : ((x25 ≤ x27) ∨ (x27 ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x25) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6710 (t x25 x27 x57 : ℝ) (h : (((x25 ≤ x27) ∧ (x27 ≤ x57) ∧ ((x57 - x25) ≥ 1) ∧ ((x27 - x25) ≤ (t - 1)) ∧ ((x57 - x27) ≤ (t - 1))) ∨ ((x57 ≤ x27) ∧ (x27 ≤ x25) ∧ ((x25 - x57) ≥ 1) ∧ ((x25 - x27) ≤ (t - 1)) ∧ ((x27 - x57) ≤ (t - 1))))) : ((x25 ≤ x27) ∨ ((x25 - x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x57) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6711 (t x25 x27 x57 : ℝ) (h : (((x25 ≤ x27) ∧ (x27 ≤ x57) ∧ ((x57 - x25) ≥ 1) ∧ ((x27 - x25) ≤ (t - 1)) ∧ ((x57 - x27) ≤ (t - 1))) ∨ ((x57 ≤ x27) ∧ (x27 ≤ x25) ∧ ((x25 - x57) ≥ 1) ∧ ((x25 - x27) ≤ (t - 1)) ∧ ((x27 - x57) ≤ (t - 1))))) : ((x25 ≤ x27) ∨ ((x25 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6712 (t x25 x27 x57 : ℝ) (h : (((x25 ≤ x27) ∧ (x27 ≤ x57) ∧ ((x57 - x25) ≥ 1) ∧ ((x27 - x25) ≤ (t - 1)) ∧ ((x57 - x27) ≤ (t - 1))) ∨ ((x57 ≤ x27) ∧ (x27 ≤ x25) ∧ ((x25 - x57) ≥ 1) ∧ ((x25 - x27) ≤ (t - 1)) ∧ ((x27 - x57) ≤ (t - 1))))) : ((x25 ≤ x27) ∨ ((x27 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6713 (t x25 x27 x57 : ℝ) (h : (((x25 ≤ x27) ∧ (x27 ≤ x57) ∧ ((x57 - x25) ≥ 1) ∧ ((x27 - x25) ≤ (t - 1)) ∧ ((x57 - x27) ≤ (t - 1))) ∨ ((x57 ≤ x27) ∧ (x27 ≤ x25) ∧ ((x25 - x57) ≥ 1) ∧ ((x25 - x27) ≤ (t - 1)) ∧ ((x27 - x57) ≤ (t - 1))))) : ((x27 ≤ x57) ∨ (x57 ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x27) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6714 (t x25 x27 x57 : ℝ) (h : (((x25 ≤ x27) ∧ (x27 ≤ x57) ∧ ((x57 - x25) ≥ 1) ∧ ((x27 - x25) ≤ (t - 1)) ∧ ((x57 - x27) ≤ (t - 1))) ∨ ((x57 ≤ x27) ∧ (x27 ≤ x25) ∧ ((x25 - x57) ≥ 1) ∧ ((x25 - x27) ≤ (t - 1)) ∧ ((x27 - x57) ≤ (t - 1))))) : ((x27 ≤ x57) ∨ (x27 ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x25) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6715 (t x25 x27 x57 : ℝ) (h : (((x25 ≤ x27) ∧ (x27 ≤ x57) ∧ ((x57 - x25) ≥ 1) ∧ ((x27 - x25) ≤ (t - 1)) ∧ ((x57 - x27) ≤ (t - 1))) ∨ ((x57 ≤ x27) ∧ (x27 ≤ x25) ∧ ((x25 - x57) ≥ 1) ∧ ((x25 - x27) ≤ (t - 1)) ∧ ((x27 - x57) ≤ (t - 1))))) : ((x27 ≤ x57) ∨ ((x25 - x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x57) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6716 (t x25 x27 x57 : ℝ) (h : (((x25 ≤ x27) ∧ (x27 ≤ x57) ∧ ((x57 - x25) ≥ 1) ∧ ((x27 - x25) ≤ (t - 1)) ∧ ((x57 - x27) ≤ (t - 1))) ∨ ((x57 ≤ x27) ∧ (x27 ≤ x25) ∧ ((x25 - x57) ≥ 1) ∧ ((x25 - x27) ≤ (t - 1)) ∧ ((x27 - x57) ≤ (t - 1))))) : ((x27 ≤ x57) ∨ ((x25 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6717 (t x25 x27 x57 : ℝ) (h : (((x25 ≤ x27) ∧ (x27 ≤ x57) ∧ ((x57 - x25) ≥ 1) ∧ ((x27 - x25) ≤ (t - 1)) ∧ ((x57 - x27) ≤ (t - 1))) ∨ ((x57 ≤ x27) ∧ (x27 ≤ x25) ∧ ((x25 - x57) ≥ 1) ∧ ((x25 - x27) ≤ (t - 1)) ∧ ((x27 - x57) ≤ (t - 1))))) : ((x27 ≤ x57) ∨ ((x27 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6718 (t x25 x27 x57 : ℝ) (h : (((x25 ≤ x27) ∧ (x27 ≤ x57) ∧ ((x57 - x25) ≥ 1) ∧ ((x27 - x25) ≤ (t - 1)) ∧ ((x57 - x27) ≤ (t - 1))) ∨ ((x57 ≤ x27) ∧ (x27 ≤ x25) ∧ ((x25 - x57) ≥ 1) ∧ ((x25 - x27) ≤ (t - 1)) ∧ ((x27 - x57) ≤ (t - 1))))) : (((x57 - x25) ≥ 1) ∨ (x57 ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x25) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x27) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6719 (t x25 x27 x57 : ℝ) (h : (((x25 ≤ x27) ∧ (x27 ≤ x57) ∧ ((x57 - x25) ≥ 1) ∧ ((x27 - x25) ≤ (t - 1)) ∧ ((x57 - x27) ≤ (t - 1))) ∨ ((x57 ≤ x27) ∧ (x27 ≤ x25) ∧ ((x25 - x57) ≥ 1) ∧ ((x25 - x27) ≤ (t - 1)) ∧ ((x27 - x57) ≤ (t - 1))))) : (((x57 - x25) ≥ 1) ∨ (x27 ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x25) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x25) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6720 (t x25 x27 x57 : ℝ) (h : (((x25 ≤ x27) ∧ (x27 ≤ x57) ∧ ((x57 - x25) ≥ 1) ∧ ((x27 - x25) ≤ (t - 1)) ∧ ((x57 - x27) ≤ (t - 1))) ∨ ((x57 ≤ x27) ∧ (x27 ≤ x25) ∧ ((x25 - x57) ≥ 1) ∧ ((x25 - x27) ≤ (t - 1)) ∧ ((x27 - x57) ≤ (t - 1))))) : (((x57 - x25) ≥ 1) ∨ ((x25 - x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x25) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x57) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6721 (t x25 x27 x57 : ℝ) (h : (((x25 ≤ x27) ∧ (x27 ≤ x57) ∧ ((x57 - x25) ≥ 1) ∧ ((x27 - x25) ≤ (t - 1)) ∧ ((x57 - x27) ≤ (t - 1))) ∨ ((x57 ≤ x27) ∧ (x27 ≤ x25) ∧ ((x25 - x57) ≥ 1) ∧ ((x25 - x27) ≤ (t - 1)) ∧ ((x27 - x57) ≤ (t - 1))))) : (((x57 - x25) ≥ 1) ∨ ((x25 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x25) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6722 (t x25 x27 x57 : ℝ) (h : (((x25 ≤ x27) ∧ (x27 ≤ x57) ∧ ((x57 - x25) ≥ 1) ∧ ((x27 - x25) ≤ (t - 1)) ∧ ((x57 - x27) ≤ (t - 1))) ∨ ((x57 ≤ x27) ∧ (x27 ≤ x25) ∧ ((x25 - x57) ≥ 1) ∧ ((x25 - x27) ≤ (t - 1)) ∧ ((x27 - x57) ≤ (t - 1))))) : (((x57 - x25) ≥ 1) ∨ ((x27 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x25) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6723 (t x25 x27 x57 : ℝ) (h : (((x25 ≤ x27) ∧ (x27 ≤ x57) ∧ ((x57 - x25) ≥ 1) ∧ ((x27 - x25) ≤ (t - 1)) ∧ ((x57 - x27) ≤ (t - 1))) ∨ ((x57 ≤ x27) ∧ (x27 ≤ x25) ∧ ((x25 - x57) ≥ 1) ∧ ((x25 - x27) ≤ (t - 1)) ∧ ((x27 - x57) ≤ (t - 1))))) : (((x27 - x25) ≤ (t - 1)) ∨ (x57 ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x25) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x27) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6724 (t x25 x27 x57 : ℝ) (h : (((x25 ≤ x27) ∧ (x27 ≤ x57) ∧ ((x57 - x25) ≥ 1) ∧ ((x27 - x25) ≤ (t - 1)) ∧ ((x57 - x27) ≤ (t - 1))) ∨ ((x57 ≤ x27) ∧ (x27 ≤ x25) ∧ ((x25 - x57) ≥ 1) ∧ ((x25 - x27) ≤ (t - 1)) ∧ ((x27 - x57) ≤ (t - 1))))) : (((x27 - x25) ≤ (t - 1)) ∨ (x27 ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x25) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x25) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6725 (t x25 x27 x57 : ℝ) (h : (((x25 ≤ x27) ∧ (x27 ≤ x57) ∧ ((x57 - x25) ≥ 1) ∧ ((x27 - x25) ≤ (t - 1)) ∧ ((x57 - x27) ≤ (t - 1))) ∨ ((x57 ≤ x27) ∧ (x27 ≤ x25) ∧ ((x25 - x57) ≥ 1) ∧ ((x25 - x27) ≤ (t - 1)) ∧ ((x27 - x57) ≤ (t - 1))))) : (((x27 - x25) ≤ (t - 1)) ∨ ((x25 - x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x25) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x57) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6726 (t x25 x27 x57 : ℝ) (h : (((x25 ≤ x27) ∧ (x27 ≤ x57) ∧ ((x57 - x25) ≥ 1) ∧ ((x27 - x25) ≤ (t - 1)) ∧ ((x57 - x27) ≤ (t - 1))) ∨ ((x57 ≤ x27) ∧ (x27 ≤ x25) ∧ ((x25 - x57) ≥ 1) ∧ ((x25 - x27) ≤ (t - 1)) ∧ ((x27 - x57) ≤ (t - 1))))) : (((x27 - x25) ≤ (t - 1)) ∨ ((x25 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x25) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6727 (t x25 x27 x57 : ℝ) (h : (((x25 ≤ x27) ∧ (x27 ≤ x57) ∧ ((x57 - x25) ≥ 1) ∧ ((x27 - x25) ≤ (t - 1)) ∧ ((x57 - x27) ≤ (t - 1))) ∨ ((x57 ≤ x27) ∧ (x27 ≤ x25) ∧ ((x25 - x57) ≥ 1) ∧ ((x25 - x27) ≤ (t - 1)) ∧ ((x27 - x57) ≤ (t - 1))))) : (((x27 - x25) ≤ (t - 1)) ∨ ((x27 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x25) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6728 (t x25 x27 x57 : ℝ) (h : (((x25 ≤ x27) ∧ (x27 ≤ x57) ∧ ((x57 - x25) ≥ 1) ∧ ((x27 - x25) ≤ (t - 1)) ∧ ((x57 - x27) ≤ (t - 1))) ∨ ((x57 ≤ x27) ∧ (x27 ≤ x25) ∧ ((x25 - x57) ≥ 1) ∧ ((x25 - x27) ≤ (t - 1)) ∧ ((x27 - x57) ≤ (t - 1))))) : (((x57 - x27) ≤ (t - 1)) ∨ (x57 ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x27) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x27) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6729 (t x25 x27 x57 : ℝ) (h : (((x25 ≤ x27) ∧ (x27 ≤ x57) ∧ ((x57 - x25) ≥ 1) ∧ ((x27 - x25) ≤ (t - 1)) ∧ ((x57 - x27) ≤ (t - 1))) ∨ ((x57 ≤ x27) ∧ (x27 ≤ x25) ∧ ((x25 - x57) ≥ 1) ∧ ((x25 - x27) ≤ (t - 1)) ∧ ((x27 - x57) ≤ (t - 1))))) : (((x57 - x27) ≤ (t - 1)) ∨ (x27 ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x27) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x25) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6730 (t x25 x27 x57 : ℝ) (h : (((x25 ≤ x27) ∧ (x27 ≤ x57) ∧ ((x57 - x25) ≥ 1) ∧ ((x27 - x25) ≤ (t - 1)) ∧ ((x57 - x27) ≤ (t - 1))) ∨ ((x57 ≤ x27) ∧ (x27 ≤ x25) ∧ ((x25 - x57) ≥ 1) ∧ ((x25 - x27) ≤ (t - 1)) ∧ ((x27 - x57) ≤ (t - 1))))) : (((x57 - x27) ≤ (t - 1)) ∨ ((x25 - x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x27) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x57) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6731 (t x25 x27 x57 : ℝ) (h : (((x25 ≤ x27) ∧ (x27 ≤ x57) ∧ ((x57 - x25) ≥ 1) ∧ ((x27 - x25) ≤ (t - 1)) ∧ ((x57 - x27) ≤ (t - 1))) ∨ ((x57 ≤ x27) ∧ (x27 ≤ x25) ∧ ((x25 - x57) ≥ 1) ∧ ((x25 - x27) ≤ (t - 1)) ∧ ((x27 - x57) ≤ (t - 1))))) : (((x57 - x27) ≤ (t - 1)) ∨ ((x25 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x27) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6732 (t x25 x27 x57 : ℝ) (h : (((x25 ≤ x27) ∧ (x27 ≤ x57) ∧ ((x57 - x25) ≥ 1) ∧ ((x27 - x25) ≤ (t - 1)) ∧ ((x57 - x27) ≤ (t - 1))) ∨ ((x57 ≤ x27) ∧ (x27 ≤ x25) ∧ ((x25 - x57) ≥ 1) ∧ ((x25 - x27) ≤ (t - 1)) ∧ ((x27 - x57) ≤ (t - 1))))) : (((x57 - x27) ≤ (t - 1)) ∨ ((x27 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x27) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6733 (x12 x23 x25 : ℝ) : ((¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th382 x12 x23 x25
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u0 u2))) h

theorem clause6735 (t x02 x12 x23 x25 x35 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x25 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th385 t x02 x12 x23 x25 x35 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u4 (And.intro u0 (And.intro u1 (And.intro u7 (And.intro u3 (And.intro u5 u2))))))))) h

theorem clause6736 (x02 x23 x25 : ℝ) : ((¬ ((x23 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x23 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th386 x02 x23 x25
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u1 u2))) h

theorem clause6737 (t x02 x05 x12 x23 x35 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x35 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x05)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th387 t x02 x05 x12 x23 x35 x56
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u4 (And.intro u7 (And.intro u0 (And.intro u6 (And.intro u3 (And.intro u1 u2)))))))) h

theorem clause6738 (t x02 x04 x05 x12 x13 x23 x24 x35 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((t + x02 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((t + ((-1) * x35) + x45) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x02 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x35) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x04 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x04 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th388 t x02 x04 x05 x12 x13 x23 x24 x35 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u0 (And.intro u4 (And.intro u10 (And.intro u9 (And.intro u1 (And.intro u7 (And.intro u2 (And.intro u5 (And.intro u3 u6)))))))))))) h

theorem clause6739 (x12 x23 : ℝ) : ((¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th389 x12 x23
  exact (fun hh => (Or.elim hh (fun hh => hh u1) (fun zz => ((fun hh => hh u0) zz)))) h

theorem clause6740 (x02 x23 : ℝ) : ((¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th390 x02 x23
  exact (fun hh => (Or.elim hh (fun hh => hh u0) (fun zz => ((fun hh => hh u1) zz)))) h

theorem clause6741 (x04 x45 : ℝ) : ((¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th391 x04 x45
  exact (fun hh => (Or.elim hh (fun hh => hh u1) (fun zz => ((fun hh => hh u0) zz)))) h

theorem clause6742 (t x02 x05 x23 x25 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + ((-1) * x23) + x25) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x23) + x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th394 t x02 x05 x23 x25 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u3 (And.intro u4 (And.intro u1 u0))))))) h

theorem clause6744 (x67 : ℝ) (h : (x67 ≥ 0)) : ((x67 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x67 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause6745 (t x12 x23 x25 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ (¬ (x67 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th397 t x12 x23 x25 x56 x67
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u1 (And.intro u2 (And.intro u6 (And.intro u3 (And.intro u5 u0))))))) h

theorem clause6746 (x05 x56 x57 : ℝ) : ((¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x57)) ≥ 0)) ∨ ((x05 + ((-1) * x57)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x05 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th399 x05 x56 x57
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause6747 (x56 x67 : ℝ) : ((¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th400 x56 x67
  exact (fun hh => (Or.elim hh (fun hh => hh u0) (fun zz => ((fun hh => hh u1) zz)))) h

theorem clause6749 (t x05 x12 x24 x25 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x24)) ≤ 0) ∨ (¬ ((x05 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ (¬ (x67 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x05 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th402 t x05 x12 x24 x25 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u4 (And.intro u6 (And.intro u0 (And.intro u3 (And.intro u7 (And.intro u5 u1))))))))) h

theorem clause6750 (t x02 x04 x05 x12 x23 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x67 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th403 t x02 x04 x05 x12 x23 x56 x67
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u7 (And.intro u8 (And.intro u6 (And.intro u4 u1))))))))) h

theorem clause6751 (t x04 x12 x24 x45 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x67 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th404 t x04 x12 x24 x45 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u6 (And.intro u4 (And.intro u3 u2))))))))) h

theorem clause6752 (t x01 x02 x12 : ℝ) : ((¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ ((t + x02 + ((-1) * x12)) ≥ 1) ∨ (¬ (x02 ≥ 0)) ∨ ((t + ((-1) * x01)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + x02 + ((-1) * x12)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th406 t x01 x02 x12
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u2 u0))))) h

theorem clause6753 (t x01 : ℝ) : ((¬ ((t + ((-1) * x01)) ≤ 0)) ∨ (t ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x01) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th407 t x01
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause6755 (t x01 : ℝ) : ((¬ (t ≤ x01)) ∨ (¬ (x01 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x01 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th408 t x01
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause6757 (t x01 : ℝ) (h : (x01 < t)) : ((x01 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 < t) := fun hh => hn hh
  exact u0 h

theorem clause6758 (t x34 x35 x45 : ℝ) : ((¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ ((t + ((-1) * x34) + x35) ≥ 1) ∨ (¬ (x35 ≥ 0)) ∨ ((t + ((-1) * x45)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x34) + x35) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th410 t x34 x35 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u2 u0))))) h

theorem clause6759 (x03 x13 x23 : ℝ) : ((¬ ((x13 + ((-1) * x23)) ≥ 0)) ∨ ((x03 + ((-1) * x13)) ≤ 0) ∨ (¬ ((x03 + ((-1) * x23)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x13 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th411 x03 x13 x23
  exact (fun hh => u1 (hh (And.intro u0 u2))) h

theorem clause6760 (t x05 x12 x25 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x25)) ≤ 0)) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ (x57 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x57 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th412 t x05 x12 x25 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u4 (And.intro u6 u7))))))))) h

theorem clause6761 (x57 : ℝ) (h : (x57 ≥ 0)) : ((x57 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x57 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause6762 (t x34 x35 x45 : ℝ) : ((¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ ((t + ((-1) * x35) + x45) ≥ 1) ∨ ((t + ((-1) * x35)) ≤ 0) ∨ (¬ (x34 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x35) + x45) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th414 t x34 x35 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u3 u0))))) h

theorem clause6763 (t x03 x35 x37 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x35) + x45) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x57)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x35) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x37 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th416 t x03 x35 x37 x45 x57
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u5 u3)))))) h

theorem clause6764 (t x13 x17 x37 : ℝ) : (((x13 + ((-1) * x17)) ≤ 0) ∨ ((x17 + ((-1) * x37)) ≥ 0) ∨ (¬ (x13 ≤ x17)) ∨ (¬ (x17 ≤ x37)) ∨ (¬ ((x37 - x13) ≥ 1)) ∨ (¬ ((x17 - x13) ≤ (t - 1))) ∨ (¬ ((x37 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th421 t x13 x17 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6766 (t x13 x17 x37 : ℝ) : (((x13 + ((-1) * x17)) ≤ 0) ∨ ((x13 + ((-1) * x37)) ≥ 1) ∨ (¬ (x13 ≤ x17)) ∨ (¬ (x17 ≤ x37)) ∨ (¬ ((x37 - x13) ≥ 1)) ∨ (¬ ((x17 - x13) ≤ (t - 1))) ∨ (¬ ((x37 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th421 t x13 x17 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6770 (t x13 x17 x37 : ℝ) : (((x17 + ((-1) * x37)) ≤ 0) ∨ ((x13 + ((-1) * x17)) ≥ 0) ∨ (¬ (x13 ≤ x17)) ∨ (¬ (x17 ≤ x37)) ∨ (¬ ((x37 - x13) ≥ 1)) ∨ (¬ ((x17 - x13) ≤ (t - 1))) ∨ (¬ ((x37 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 + ((-1) * x37)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x17)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th421 t x13 x17 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6771 (t x13 x17 x37 : ℝ) : (((x13 + ((-1) * x37)) ≥ 1) ∨ ((x17 + ((-1) * x37)) ≤ 0) ∨ (¬ (x13 ≤ x17)) ∨ (¬ (x17 ≤ x37)) ∨ (¬ ((x37 - x13) ≥ 1)) ∨ (¬ ((x17 - x13) ≤ (t - 1))) ∨ (¬ ((x37 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x37)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th421 t x13 x17 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6774 (t x13 x17 x37 : ℝ) : (((x13 + ((-1) * x37)) ≤ (-1)) ∨ ((x17 + ((-1) * x37)) ≥ 0) ∨ (¬ (x13 ≤ x17)) ∨ (¬ (x17 ≤ x37)) ∨ (¬ ((x37 - x13) ≥ 1)) ∨ (¬ ((x17 - x13) ≤ (t - 1))) ∨ (¬ ((x37 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th421 t x13 x17 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6775 (t x13 x17 x37 : ℝ) : (((x13 + ((-1) * x37)) ≤ (-1)) ∨ ((x13 + ((-1) * x17)) ≥ 0) ∨ (¬ (x13 ≤ x17)) ∨ (¬ (x17 ≤ x37)) ∨ (¬ ((x37 - x13) ≥ 1)) ∨ (¬ ((x17 - x13) ≤ (t - 1))) ∨ (¬ ((x37 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x17)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th421 t x13 x17 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6776 (t x13 x17 x37 : ℝ) : (((x13 + ((-1) * x37)) ≥ 1) ∨ ((x13 + ((-1) * x37)) ≤ (-1)) ∨ (¬ (x13 ≤ x17)) ∨ (¬ (x17 ≤ x37)) ∨ (¬ ((x37 - x13) ≥ 1)) ∨ (¬ ((x17 - x13) ≤ (t - 1))) ∨ (¬ ((x37 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th421 t x13 x17 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6777 (t x13 x17 x37 : ℝ) : (((x13 + ((-1) * x37)) ≤ (-1)) ∨ ((t + ((-1) * x13) + x17) ≥ 1) ∨ (¬ (x13 ≤ x17)) ∨ (¬ (x17 ≤ x37)) ∨ (¬ ((x37 - x13) ≥ 1)) ∨ (¬ ((x17 - x13) ≤ (t - 1))) ∨ (¬ ((x37 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x13) + x17) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th421 t x13 x17 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6778 (t x13 x17 x37 : ℝ) : (((x13 + ((-1) * x37)) ≤ (-1)) ∨ ((t + ((-1) * x17) + x37) ≥ 1) ∨ (¬ (x13 ≤ x17)) ∨ (¬ (x17 ≤ x37)) ∨ (¬ ((x37 - x13) ≥ 1)) ∨ (¬ ((x17 - x13) ≤ (t - 1))) ∨ (¬ ((x37 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x17) + x37) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th421 t x13 x17 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6786 (t x13 x17 x37 : ℝ) : (((x13 + ((-1) * x37)) ≥ 1) ∨ ((t + x17 + ((-1) * x37)) ≥ 1) ∨ (¬ (x13 ≤ x17)) ∨ (¬ (x17 ≤ x37)) ∨ (¬ ((x37 - x13) ≥ 1)) ∨ (¬ ((x17 - x13) ≤ (t - 1))) ∨ (¬ ((x37 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x17 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th421 t x13 x17 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6789 (t x13 x17 x37 : ℝ) : (((x13 + ((-1) * x17)) ≤ 0) ∨ ((x17 + ((-1) * x37)) ≥ 0) ∨ (¬ (x37 ≤ x17)) ∨ (¬ (x17 ≤ x13)) ∨ (¬ ((x13 - x37) ≥ 1)) ∨ (¬ ((x13 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th421 t x13 x17 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6791 (t x13 x17 x37 : ℝ) : (((x13 + ((-1) * x17)) ≤ 0) ∨ ((x13 + ((-1) * x37)) ≥ 1) ∨ (¬ (x37 ≤ x17)) ∨ (¬ (x17 ≤ x13)) ∨ (¬ ((x13 - x37) ≥ 1)) ∨ (¬ ((x13 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th421 t x13 x17 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6795 (t x13 x17 x37 : ℝ) : (((x17 + ((-1) * x37)) ≤ 0) ∨ ((x13 + ((-1) * x17)) ≥ 0) ∨ (¬ (x37 ≤ x17)) ∨ (¬ (x17 ≤ x13)) ∨ (¬ ((x13 - x37) ≥ 1)) ∨ (¬ ((x13 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 + ((-1) * x37)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x17)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th421 t x13 x17 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6796 (t x13 x17 x37 : ℝ) : (((x13 + ((-1) * x37)) ≥ 1) ∨ ((x17 + ((-1) * x37)) ≤ 0) ∨ (¬ (x37 ≤ x17)) ∨ (¬ (x17 ≤ x13)) ∨ (¬ ((x13 - x37) ≥ 1)) ∨ (¬ ((x13 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x37)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th421 t x13 x17 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6799 (t x13 x17 x37 : ℝ) : (((x13 + ((-1) * x37)) ≤ (-1)) ∨ ((x17 + ((-1) * x37)) ≥ 0) ∨ (¬ (x37 ≤ x17)) ∨ (¬ (x17 ≤ x13)) ∨ (¬ ((x13 - x37) ≥ 1)) ∨ (¬ ((x13 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th421 t x13 x17 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6800 (t x13 x17 x37 : ℝ) : (((x13 + ((-1) * x37)) ≤ (-1)) ∨ ((x13 + ((-1) * x17)) ≥ 0) ∨ (¬ (x37 ≤ x17)) ∨ (¬ (x17 ≤ x13)) ∨ (¬ ((x13 - x37) ≥ 1)) ∨ (¬ ((x13 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x17)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th421 t x13 x17 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6801 (t x13 x17 x37 : ℝ) : (((x13 + ((-1) * x37)) ≥ 1) ∨ ((x13 + ((-1) * x37)) ≤ (-1)) ∨ (¬ (x37 ≤ x17)) ∨ (¬ (x17 ≤ x13)) ∨ (¬ ((x13 - x37) ≥ 1)) ∨ (¬ ((x13 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th421 t x13 x17 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6802 (t x13 x17 x37 : ℝ) : (((x13 + ((-1) * x37)) ≤ (-1)) ∨ ((t + ((-1) * x13) + x17) ≥ 1) ∨ (¬ (x37 ≤ x17)) ∨ (¬ (x17 ≤ x13)) ∨ (¬ ((x13 - x37) ≥ 1)) ∨ (¬ ((x13 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x13) + x17) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th421 t x13 x17 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6803 (t x13 x17 x37 : ℝ) : (((x13 + ((-1) * x37)) ≤ (-1)) ∨ ((t + ((-1) * x17) + x37) ≥ 1) ∨ (¬ (x37 ≤ x17)) ∨ (¬ (x17 ≤ x13)) ∨ (¬ ((x13 - x37) ≥ 1)) ∨ (¬ ((x13 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x17) + x37) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th421 t x13 x17 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6811 (t x13 x17 x37 : ℝ) : (((x13 + ((-1) * x37)) ≥ 1) ∨ ((t + x17 + ((-1) * x37)) ≥ 1) ∨ (¬ (x37 ≤ x17)) ∨ (¬ (x17 ≤ x13)) ∨ (¬ ((x13 - x37) ≥ 1)) ∨ (¬ ((x13 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x17 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th421 t x13 x17 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6864 (t x13 x17 x37 : ℝ) (h : (((x13 ≤ x17) ∧ (x17 ≤ x37) ∧ ((x37 - x13) ≥ 1) ∧ ((x17 - x13) ≤ (t - 1)) ∧ ((x37 - x17) ≤ (t - 1))) ∨ ((x37 ≤ x17) ∧ (x17 ≤ x13) ∧ ((x13 - x37) ≥ 1) ∧ ((x13 - x17) ≤ (t - 1)) ∧ ((x17 - x37) ≤ (t - 1))))) : ((x13 ≤ x17) ∨ (x37 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6865 (t x13 x17 x37 : ℝ) (h : (((x13 ≤ x17) ∧ (x17 ≤ x37) ∧ ((x37 - x13) ≥ 1) ∧ ((x17 - x13) ≤ (t - 1)) ∧ ((x37 - x17) ≤ (t - 1))) ∨ ((x37 ≤ x17) ∧ (x17 ≤ x13) ∧ ((x13 - x37) ≥ 1) ∧ ((x13 - x17) ≤ (t - 1)) ∧ ((x17 - x37) ≤ (t - 1))))) : ((x13 ≤ x17) ∨ (x17 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6866 (t x13 x17 x37 : ℝ) (h : (((x13 ≤ x17) ∧ (x17 ≤ x37) ∧ ((x37 - x13) ≥ 1) ∧ ((x17 - x13) ≤ (t - 1)) ∧ ((x37 - x17) ≤ (t - 1))) ∨ ((x37 ≤ x17) ∧ (x17 ≤ x13) ∧ ((x13 - x37) ≥ 1) ∧ ((x13 - x17) ≤ (t - 1)) ∧ ((x17 - x37) ≤ (t - 1))))) : ((x13 ≤ x17) ∨ ((x13 - x37) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x37) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6867 (t x13 x17 x37 : ℝ) (h : (((x13 ≤ x17) ∧ (x17 ≤ x37) ∧ ((x37 - x13) ≥ 1) ∧ ((x17 - x13) ≤ (t - 1)) ∧ ((x37 - x17) ≤ (t - 1))) ∨ ((x37 ≤ x17) ∧ (x17 ≤ x13) ∧ ((x13 - x37) ≥ 1) ∧ ((x13 - x17) ≤ (t - 1)) ∧ ((x17 - x37) ≤ (t - 1))))) : ((x13 ≤ x17) ∨ ((x13 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6868 (t x13 x17 x37 : ℝ) (h : (((x13 ≤ x17) ∧ (x17 ≤ x37) ∧ ((x37 - x13) ≥ 1) ∧ ((x17 - x13) ≤ (t - 1)) ∧ ((x37 - x17) ≤ (t - 1))) ∨ ((x37 ≤ x17) ∧ (x17 ≤ x13) ∧ ((x13 - x37) ≥ 1) ∧ ((x13 - x17) ≤ (t - 1)) ∧ ((x17 - x37) ≤ (t - 1))))) : ((x13 ≤ x17) ∨ ((x17 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6869 (t x13 x17 x37 : ℝ) (h : (((x13 ≤ x17) ∧ (x17 ≤ x37) ∧ ((x37 - x13) ≥ 1) ∧ ((x17 - x13) ≤ (t - 1)) ∧ ((x37 - x17) ≤ (t - 1))) ∨ ((x37 ≤ x17) ∧ (x17 ≤ x13) ∧ ((x13 - x37) ≥ 1) ∧ ((x13 - x17) ≤ (t - 1)) ∧ ((x17 - x37) ≤ (t - 1))))) : ((x17 ≤ x37) ∨ (x37 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6870 (t x13 x17 x37 : ℝ) (h : (((x13 ≤ x17) ∧ (x17 ≤ x37) ∧ ((x37 - x13) ≥ 1) ∧ ((x17 - x13) ≤ (t - 1)) ∧ ((x37 - x17) ≤ (t - 1))) ∨ ((x37 ≤ x17) ∧ (x17 ≤ x13) ∧ ((x13 - x37) ≥ 1) ∧ ((x13 - x17) ≤ (t - 1)) ∧ ((x17 - x37) ≤ (t - 1))))) : ((x17 ≤ x37) ∨ (x17 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6871 (t x13 x17 x37 : ℝ) (h : (((x13 ≤ x17) ∧ (x17 ≤ x37) ∧ ((x37 - x13) ≥ 1) ∧ ((x17 - x13) ≤ (t - 1)) ∧ ((x37 - x17) ≤ (t - 1))) ∨ ((x37 ≤ x17) ∧ (x17 ≤ x13) ∧ ((x13 - x37) ≥ 1) ∧ ((x13 - x17) ≤ (t - 1)) ∧ ((x17 - x37) ≤ (t - 1))))) : ((x17 ≤ x37) ∨ ((x13 - x37) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x37) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6872 (t x13 x17 x37 : ℝ) (h : (((x13 ≤ x17) ∧ (x17 ≤ x37) ∧ ((x37 - x13) ≥ 1) ∧ ((x17 - x13) ≤ (t - 1)) ∧ ((x37 - x17) ≤ (t - 1))) ∨ ((x37 ≤ x17) ∧ (x17 ≤ x13) ∧ ((x13 - x37) ≥ 1) ∧ ((x13 - x17) ≤ (t - 1)) ∧ ((x17 - x37) ≤ (t - 1))))) : ((x17 ≤ x37) ∨ ((x13 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6873 (t x13 x17 x37 : ℝ) (h : (((x13 ≤ x17) ∧ (x17 ≤ x37) ∧ ((x37 - x13) ≥ 1) ∧ ((x17 - x13) ≤ (t - 1)) ∧ ((x37 - x17) ≤ (t - 1))) ∨ ((x37 ≤ x17) ∧ (x17 ≤ x13) ∧ ((x13 - x37) ≥ 1) ∧ ((x13 - x17) ≤ (t - 1)) ∧ ((x17 - x37) ≤ (t - 1))))) : ((x17 ≤ x37) ∨ ((x17 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6874 (t x13 x17 x37 : ℝ) (h : (((x13 ≤ x17) ∧ (x17 ≤ x37) ∧ ((x37 - x13) ≥ 1) ∧ ((x17 - x13) ≤ (t - 1)) ∧ ((x37 - x17) ≤ (t - 1))) ∨ ((x37 ≤ x17) ∧ (x17 ≤ x13) ∧ ((x13 - x37) ≥ 1) ∧ ((x13 - x17) ≤ (t - 1)) ∧ ((x17 - x37) ≤ (t - 1))))) : (((x37 - x13) ≥ 1) ∨ (x37 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x13) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6875 (t x13 x17 x37 : ℝ) (h : (((x13 ≤ x17) ∧ (x17 ≤ x37) ∧ ((x37 - x13) ≥ 1) ∧ ((x17 - x13) ≤ (t - 1)) ∧ ((x37 - x17) ≤ (t - 1))) ∨ ((x37 ≤ x17) ∧ (x17 ≤ x13) ∧ ((x13 - x37) ≥ 1) ∧ ((x13 - x17) ≤ (t - 1)) ∧ ((x17 - x37) ≤ (t - 1))))) : (((x37 - x13) ≥ 1) ∨ (x17 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x13) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6876 (t x13 x17 x37 : ℝ) (h : (((x13 ≤ x17) ∧ (x17 ≤ x37) ∧ ((x37 - x13) ≥ 1) ∧ ((x17 - x13) ≤ (t - 1)) ∧ ((x37 - x17) ≤ (t - 1))) ∨ ((x37 ≤ x17) ∧ (x17 ≤ x13) ∧ ((x13 - x37) ≥ 1) ∧ ((x13 - x17) ≤ (t - 1)) ∧ ((x17 - x37) ≤ (t - 1))))) : (((x37 - x13) ≥ 1) ∨ ((x13 - x37) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x13) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x37) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6877 (t x13 x17 x37 : ℝ) (h : (((x13 ≤ x17) ∧ (x17 ≤ x37) ∧ ((x37 - x13) ≥ 1) ∧ ((x17 - x13) ≤ (t - 1)) ∧ ((x37 - x17) ≤ (t - 1))) ∨ ((x37 ≤ x17) ∧ (x17 ≤ x13) ∧ ((x13 - x37) ≥ 1) ∧ ((x13 - x17) ≤ (t - 1)) ∧ ((x17 - x37) ≤ (t - 1))))) : (((x37 - x13) ≥ 1) ∨ ((x13 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x13) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6878 (t x13 x17 x37 : ℝ) (h : (((x13 ≤ x17) ∧ (x17 ≤ x37) ∧ ((x37 - x13) ≥ 1) ∧ ((x17 - x13) ≤ (t - 1)) ∧ ((x37 - x17) ≤ (t - 1))) ∨ ((x37 ≤ x17) ∧ (x17 ≤ x13) ∧ ((x13 - x37) ≥ 1) ∧ ((x13 - x17) ≤ (t - 1)) ∧ ((x17 - x37) ≤ (t - 1))))) : (((x37 - x13) ≥ 1) ∨ ((x17 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x13) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6879 (t x13 x17 x37 : ℝ) (h : (((x13 ≤ x17) ∧ (x17 ≤ x37) ∧ ((x37 - x13) ≥ 1) ∧ ((x17 - x13) ≤ (t - 1)) ∧ ((x37 - x17) ≤ (t - 1))) ∨ ((x37 ≤ x17) ∧ (x17 ≤ x13) ∧ ((x13 - x37) ≥ 1) ∧ ((x13 - x17) ≤ (t - 1)) ∧ ((x17 - x37) ≤ (t - 1))))) : (((x17 - x13) ≤ (t - 1)) ∨ (x37 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6880 (t x13 x17 x37 : ℝ) (h : (((x13 ≤ x17) ∧ (x17 ≤ x37) ∧ ((x37 - x13) ≥ 1) ∧ ((x17 - x13) ≤ (t - 1)) ∧ ((x37 - x17) ≤ (t - 1))) ∨ ((x37 ≤ x17) ∧ (x17 ≤ x13) ∧ ((x13 - x37) ≥ 1) ∧ ((x13 - x17) ≤ (t - 1)) ∧ ((x17 - x37) ≤ (t - 1))))) : (((x17 - x13) ≤ (t - 1)) ∨ (x17 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6881 (t x13 x17 x37 : ℝ) (h : (((x13 ≤ x17) ∧ (x17 ≤ x37) ∧ ((x37 - x13) ≥ 1) ∧ ((x17 - x13) ≤ (t - 1)) ∧ ((x37 - x17) ≤ (t - 1))) ∨ ((x37 ≤ x17) ∧ (x17 ≤ x13) ∧ ((x13 - x37) ≥ 1) ∧ ((x13 - x17) ≤ (t - 1)) ∧ ((x17 - x37) ≤ (t - 1))))) : (((x17 - x13) ≤ (t - 1)) ∨ ((x13 - x37) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x37) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

#print axioms clause6881
end NineCNFDirectTrial
