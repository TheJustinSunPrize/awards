import NineTheoryTrial

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineCNFDirectTrial

theorem clause13030 (t x03 x34 x35 x45 x57 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1)))) := by
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
  have u3 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5503 t x03 x34 x35 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u2 (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u3 u0)))))))) h

theorem clause13031 (t x02 x03 x23 : ℝ) : (((t + x03 + ((-1) * x23)) ≥ 1) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x03 ≥ 0)) ∨ ((t + ((-1) * x02)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x03 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th5507 t x02 x03 x23
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u3 u0))))) h

theorem clause13032 (x35 x45 x57 : ℝ) : (((x35 + ((-1) * x57)) ≥ 1) ∨ (¬ ((x35 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5509 x35 x45 x57
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause13033 (t x25 x45 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x25) + x45) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x25) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5510 t x25 x45 x46 x56 x67
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u5 (And.intro u3 (And.intro u0 (And.intro u4 u1)))))) h

theorem clause13035 (t x03 x06 x34 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + x34 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x34 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5515 t x03 x06 x34 x36 x67
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u4 (And.intro u0 (And.intro u1 (And.intro u3 u5)))))) h

theorem clause13036 (x34 x36 x47 x67 : ℝ) : ((¬ ((x34 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x47 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x47 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th5517 x34 x36 x47 x67
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u1 (And.intro u3 u2)))) h

theorem clause13038 (t x03 x06 x34 x35 x36 x67 : ℝ) : ((¬ ((x35 + ((-1) * x36)) ≥ 0)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + x34 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + x34 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5521 t x03 x06 x34 x35 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u3 (And.intro u4 (And.intro u5 (And.intro u6 u0)))))))) h

theorem clause13040 (t x02 x12 x23 x24 x27 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((t + x23 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x23 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5523 t x02 x12 x23 x24 x27
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u4 u5))))))) h

theorem clause13041 (t x02 x26 x27 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((t + x26 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x26 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x27 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5524 t x02 x26 x27 x36 x67
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u3 u2)))))) h

theorem clause13042 (t x03 x06 x23 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x03 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x03 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5525 t x03 x06 x23 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u5 u4))))))) h

theorem clause13043 (t x02 x23 x24 x34 x35 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x34) + x35) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
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
  have u5 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5526 t x02 x23 x24 x34 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u4 u2))))))) h

theorem clause13044 (t x06 x34 x36 x45 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((t + ((-1) * x45) + x46) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x45) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5527 t x06 x34 x36 x45 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u4 (And.intro u6 (And.intro u2 (And.intro u5 u1)))))))) h

theorem clause13045 (x36 x46 x67 : ℝ) : ((¬ ((x36 + ((-1) * x46)) ≤ 0)) ∨ ((x46 + ((-1) * x67)) ≥ 1) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x36 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x46 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5529 x36 x46 x67
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause13046 (t x03 x12 x23 x24 x34 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((t + x03 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x03 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5531 t x03 x12 x23 x24 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u3 (And.intro u4 u5))))))) h

theorem clause13047 (t x16 x23 x36 x37 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x67)) ≥ 0)) ∨ (¬ ((t + x16 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x37 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x16 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5537 t x16 x23 x36 x37 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u4 (And.intro u1 u3))))))) h

theorem clause13048 (t x02 x23 x35 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ (x02 ≥ 0)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5539 t x02 x23 x35 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u4 (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u2 u3)))))))) h

theorem clause13049 (t x16 x56 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x56 + ((-1) * x57)) ≥ 0)) ∨ (¬ ((t + x16 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x16 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5540 t x16 x56 x57 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u0 (And.intro u3 (And.intro u2 u4))))))) h

theorem clause13050 (t x06 x07 x36 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x06 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((t + x06 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x06 + ((-1) * x07)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x06 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5541 t x06 x07 x36 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u5 u4))))))) h

theorem clause13051 (t x02 x23 x34 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ (x02 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5542 t x02 x23 x34 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u1 (And.intro u6 (And.intro u3 u2)))))))) h

theorem clause13053 (t x01 x02 x12 : ℝ) : (((t + ((-1) * x01) + x02) ≥ 1) ∨ (¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ (x01 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x01) + x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x02)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hh))))
  have h := NineTheoryTrial.th5547 t x01 x02 x12
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u4 (And.intro u2 u1)))))) h

theorem clause13054 (t x01 x02 x17 x24 x45 x58 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x58)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x58) + x78) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x58) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5548 t x01 x02 x17 x24 x45 x58 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u0 (And.intro u7 (And.intro u6 (And.intro u1 (And.intro u3 u4))))))))) h

theorem clause13055 (t x07 x16 x17 x36 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x07 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + x16 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x17)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x07 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x07 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x16 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 + ((-1) * x17)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5550 t x07 x16 x17 x36 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u3 (And.intro u4 (And.intro u2 (And.intro u0 u6)))))))) h

theorem clause13056 (t x01 x02 x17 x23 x35 x58 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x58) + x78) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x58) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5551 t x01 x02 x17 x23 x35 x58 x78
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u5 (And.intro u4 (And.intro u7 u0)))))))) h

theorem clause13057 (t x02 x23 x25 x35 x56 x57 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ (x02 ≥ 0)) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x35 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x57)) ≥ 0)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th5552 t x02 x23 x25 x35 x56 x57 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u4 (And.intro u1 (And.intro u5 (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u6 u8)))))))))) h

theorem clause13058 (t x05 x23 x34 x35 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x05)) ≤ 0) ∨ (¬ (x34 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x05)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5553 t x05 x23 x34 x35 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u2 (And.intro u6 (And.intro u4 u3)))))))) h

theorem clause13059 (x36 x56 x67 : ℝ) : ((¬ ((x36 + ((-1) * x56)) ≤ 0)) ∨ ((x56 + ((-1) * x67)) ≥ 1) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x36 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x56 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5554 x36 x56 x67
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause13060 (t x06 x15 x35 x36 x56 x67 : ℝ) : ((¬ ((x35 + ((-1) * x36)) ≥ 0)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((t + x15 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x15 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5555 t x06 x15 x35 x36 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u6 (And.intro u2 (And.intro u5 u3)))))))) h

theorem clause13062 (t x03 x14 x34 x45 x46 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ (x03 ≥ 0)) ∨ ((t + ((-1) * x45)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x03 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5557 t x03 x14 x34 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u4 (And.intro u6 (And.intro u2 (And.intro u3 u0)))))))) h

theorem clause13063 (t x02 x23 x35 x56 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ (x02 ≥ 0)) ∨ ((t + ((-1) * x68)) ≤ 0) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5562 t x02 x23 x35 x56 x68
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u3 (And.intro u6 (And.intro u5 (And.intro u4 (And.intro u0 u1))))))) h

theorem clause13064 (t x06 x13 x36 x37 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((t + x06 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x67)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x06 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5564 t x06 x13 x36 x37 x67
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u4 (And.intro u0 (And.intro u5 (And.intro u1 u3)))))) h

theorem clause13065 (t x13 x23 x35 x37 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5565 t x13 x23 x35 x37 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u0 (And.intro u4 (And.intro u5 (And.intro u2 (And.intro u3 u1)))))))) h

theorem clause13066 (t x01 x13 x35 x56 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ ((t + ((-1) * x68)) ≤ 0) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1))) ∨ (¬ (x01 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5566 t x01 x13 x35 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u6 (And.intro u1 (And.intro u4 (And.intro u0 u2)))))))) h

theorem clause13067 (t x02 x05 x06 x23 x24 x36 x45 x48 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x68)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((t + x45 + ((-1) * x48)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x48)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x05 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((t + x45 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))))
  have u12 : ((x24 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))))
  have h := NineTheoryTrial.th5567 t x02 x05 x06 x23 x24 x36 x45 x48 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u8 (And.intro u7 (And.intro u6 (And.intro u5 (And.intro u0 (And.intro u11 (And.intro u9 (And.intro u3 (And.intro u12 (And.intro u2 (And.intro u10 u1)))))))))))))) h

theorem clause13068 (t x12 x14 x23 x24 x48 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((t + x23 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x48)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x48)) ≥ 1))) := by
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
  have u3 : ((x12 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5570 t x12 x14 x23 x24 x48
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u3 (And.intro u4 (And.intro u0 (And.intro u2 u1)))))) h

theorem clause13070 (t x01 x03 x05 x06 x14 x36 x48 x56 x67 x68 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x48 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x48)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x48 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x05 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x14 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th5574 t x01 x03 x05 x06 x14 x36 x48 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u8 (And.intro u9 (And.intro u10 (And.intro u7 (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u2 u6)))))))))))) h

theorem clause13071 (x25 x35 x56 : ℝ) : ((¬ ((x25 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x25 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5578 x25 x35 x56
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u0 u1))) h

theorem clause13072 (x35 x36 x57 x67 : ℝ) : ((¬ ((x35 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x57 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x57 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th5580 x35 x36 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u0 u2))))) h

theorem clause13073 (t x24 x34 x36 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x24 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x24 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5582 t x24 x34 x36 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u4 u5))))))) h

theorem clause13074 (x04 x24 x46 : ℝ) : ((¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5583 x04 x24 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause13075 (t x02 x23 x24 x37 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x24 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x24 ≥ 0) := by
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
  have u4 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5588 t x02 x23 x24 x37 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u4 (And.intro u5 (And.intro u2 (And.intro u6 u3)))))))) h

theorem clause13076 (t x06 x12 x23 x26 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x26)) ≥ 0)) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5589 t x06 x12 x23 x26 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u4 (And.intro u2 u6))))))))) h

theorem clause13077 (t x02 x25 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x02 ≥ 0)) ∨ ((t + ((-1) * x46)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5590 t x02 x25 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u1 (And.intro u3 (And.intro u0 (And.intro u4 u6)))))))) h

theorem clause13078 (t x25 x45 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x25 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x25 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5591 t x25 x45 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u1 u4))))))) h

theorem clause13079 (t x02 x12 x23 x26 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x12 ≥ 0) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5596 t x02 x12 x23 x26 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u6 (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u2 u3)))))))) h

theorem clause13080 (x46 x56 x67 : ℝ) : ((¬ ((x46 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ ((x46 + ((-1) * x67)) ≤ (-1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x46 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x46 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5597 x46 x56 x67
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause13081 (x34 x45 x46 : ℝ) : ((¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ ((x34 + ((-1) * x46)) ≥ 1) ∨ (¬ ((x45 + ((-1) * x46)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5598 x34 x45 x46
  exact (fun hh => u1 (hh (And.intro u0 u2))) h

theorem clause13082 (t x01 x12 x13 x34 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ (x12 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5599 t x01 x12 x13 x34 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u0 (And.intro u2 (And.intro u1 (And.intro u4 (And.intro u5 u3)))))))) h

theorem clause13083 (t x14 x16 x34 x45 x46 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x14 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x45) + x46) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x16)) ≥ 0)) ∨ (¬ ((x16 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x45) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5600 t x14 x16 x34 x45 x46 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u6 (And.intro u0 (And.intro u5 u4)))))))) h

theorem clause13084 (t x03 x34 x36 x45 x46 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((t + ((-1) * x45) + x46) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1))) := by
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
  have u3 : ((x36 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x45) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5601 t x03 x34 x36 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u2 u3))))))) h

theorem clause13085 (t x03 x13 x14 x34 x35 x45 x56 x57 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((t + x03 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x03 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x56 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th5602 t x03 x13 x14 x34 x35 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u1 (And.intro u7 (And.intro u3 (And.intro u6 (And.intro u2 (And.intro u8 u5)))))))))) h

theorem clause13086 (t x04 x05 x45 x46 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((t + ((-1) * x45) + x46) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x45) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5604 t x04 x05 x45 x46 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u5 (And.intro u4 u1))))))) h

theorem clause13087 (t x02 x13 x23 x25 x35 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((t + ((-1) * x13) + x23) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x13) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x25 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5605 t x02 x13 x23 x25 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u4 (And.intro u3 u5))))))) h

theorem clause13088 (t x12 x25 x35 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5606 t x12 x25 x35 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u6 (And.intro u4 (And.intro u0 (And.intro u1 (And.intro u5 u3)))))))) h

theorem clause13089 (t x12 x26 x27 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + x26 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x26 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x27 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5608 t x12 x26 x27 x46 x67
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u3 u5)))))) h

theorem clause13090 (x12 x24 x26 : ℝ) : ((¬ ((x24 + ((-1) * x26)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x24 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5611 x12 x24 x26
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 u0)))) h

theorem clause13092 (x16 x46 x67 : ℝ) : ((¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x16 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5614 x16 x46 x67
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u2 u0))) h

theorem clause13094 (t x04 x06 x13 x16 x34 x35 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((t + ((-1) * x34) + x35) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x06)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x16)) ≤ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x34) + x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5621 t x04 x06 x13 x16 x34 x35 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u6 (And.intro u7 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u4 u2))))))))) h

theorem clause13095 (t x02 x12 x16 x24 x26 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x12) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x16)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x02) + x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5622 t x02 x12 x16 x24 x26 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u6 (And.intro u5 u4)))))))) h

theorem clause13096 (t x01 x12 x26 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x46 ≥ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5623 t x01 x12 x26 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u6 (And.intro u0 (And.intro u5 (And.intro u1 u2)))))))) h

theorem clause13097 (t x06 x24 x46 x47 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + ((-1) * x06) + x46) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1))) := by
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
  have u3 : ((t + ((-1) * x06) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5624 t x06 x24 x46 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u5 (And.intro u0 (And.intro u1 u4))))))) h

theorem clause13099 (t x01 x12 x24 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ (x78 ≥ 0)) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5626 t x01 x12 x24 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u6 u4)))))))) h

theorem clause13100 (t x01 x05 x12 x24 x47 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x47 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x05) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x47 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x01) + x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5627 t x01 x05 x12 x24 x47 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u6 (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u1 (And.intro u7 u3))))))))) h

theorem clause13101 (x07 x08 x17 x78 : ℝ) : ((¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x17)) ≥ 0)) ∨ (¬ ((x07 + ((-1) * x08)) ≤ 0)) ∨ (¬ ((x08 + ((-1) * x78)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x07 + ((-1) * x17)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x07 + ((-1) * x08)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x08 + ((-1) * x78)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th5630 x07 x08 x17 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u1 u3))))) h

theorem clause13102 (x47 x67 x78 : ℝ) : ((¬ ((x47 + ((-1) * x67)) ≥ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x47 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5635 x47 x67 x78
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u2 u1))) h

theorem clause13103 (t x36 x46 x47 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x36) + x46) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x47)) ≤ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x36) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x47)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5636 t x36 x46 x47 x67 x78
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u3 (And.intro u0 (And.intro u4 (And.intro u5 u1)))))) h

theorem clause13104 (t x02 x03 x12 x13 x24 x26 x35 x36 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((t + x26 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x26 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th5637 t x02 x03 x12 x13 x24 x26 x35 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u8 (And.intro u9 (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u2 (And.intro u3 (And.intro u7 u6))))))))))) h

theorem clause13105 (x03 x13 x36 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5639 x03 x13 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 u0)))) h

theorem clause13106 (t x01 x03 x12 x24 x35 x46 x56 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + x46 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x46)) ≥ 1) := by
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
  have u6 : ((t + x46 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5640 t x01 x03 x12 x24 x35 x46 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u6 (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u7 u4))))))))) h

theorem clause13107 (t x03 x23 x24 x34 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((t + ((-1) * x03) + x23) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x03) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5643 t x03 x23 x24 x34 x45
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u1 u5)))))) h

theorem clause13109 (t x01 x06 x12 x25 x36 x56 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x36) + x56) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x06) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x57)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x36) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x01) + x06) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th5646 t x01 x06 x12 x25 x36 x56 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u5 (And.intro u3 (And.intro u7 (And.intro u1 (And.intro u2 (And.intro u4 (And.intro u0 u6)))))))))) h

theorem clause13110 (t x01 x03 x12 x25 x36 x57 x67 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5647 t x01 x03 x12 x25 x36 x57 x67
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u0 (And.intro u5 (And.intro u3 (And.intro u2 (And.intro u6 (And.intro u1 u7)))))))) h

theorem clause13111 (x24 x45 x47 : ℝ) : ((¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x47)) ≤ 0)) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x47)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5650 x24 x45 x47
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u0 u2))) h

theorem clause13113 (t x01 x03 x13 x14 x36 x37 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + ((-1) * x37) + x57) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x37) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th5654 t x01 x03 x13 x14 x36 x37 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u3 (And.intro u4 (And.intro u2 (And.intro u0 (And.intro u6 (And.intro u8 (And.intro u5 (And.intro u9 u1))))))))))) h

theorem clause13114 (t x03 x16 x36 x67 x68 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ (x03 ≥ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x03 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5660 t x03 x16 x36 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u4 (And.intro u5 (And.intro u1 (And.intro u6 (And.intro u3 u0)))))))) h

theorem clause13116 (t x03 x13 x34 x35 x45 x56 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ (x03 ≥ 0))) := by
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
  have u3 : ((x35 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x03 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5667 t x03 x13 x34 x35 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u2 (And.intro u1 (And.intro u6 (And.intro u3 (And.intro u0 (And.intro u5 u4))))))))) h

theorem clause13117 (x13 x23 x26 x36 : ℝ) : ((¬ ((x13 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x26)) ≤ 0)) ∨ (¬ ((x26 + ((-1) * x36)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x13 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x26 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th5672 x13 x23 x26 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u2 u0))))) h

theorem clause13118 (t x03 x34 x36 x45 x67 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x67 ≥ 0))) := by
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
  have u3 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5673 t x03 x34 x36 x45 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u5 u6)))))))) h

theorem clause13121 (t x03 x13 x14 x34 x46 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((t + x03 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x03 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5682 t x03 x13 x14 x34 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u1 (And.intro u0 (And.intro u4 u5))))))) h

theorem clause13122 (t x13 x34 x45 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ ((t + ((-1) * x13)) ≤ 0) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x67 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5685 t x13 x34 x45 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u6 u5)))))))) h

theorem clause13124 (t x13 x35 x45 x56 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ ((t + ((-1) * x13)) ≤ 0) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5693 t x13 x35 x45 x56 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u4 (And.intro u6 (And.intro u2 (And.intro u0 u5)))))))) h

theorem clause13126 (t x03 x04 x13 x17 x34 x37 x45 x58 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + x03 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((t + x58 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x03 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x58 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x45 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x17 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th5697 t x03 x04 x13 x17 x34 x37 x45 x58 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u9 (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u8 (And.intro u7 (And.intro u4 (And.intro u6 (And.intro u5 u3))))))))))) h

theorem clause13127 (t x13 x35 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ ((t + ((-1) * x13)) ≤ 0) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ (x57 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x57 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5698 t x13 x35 x45 x56 x57
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u2 (And.intro u5 (And.intro u6 (And.intro u1 (And.intro u0 u3))))))) h

theorem clause13128 (x16 x36 x67 : ℝ) : (((x36 + ((-1) * x67)) ≤ (-1)) ∨ (¬ ((x16 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ((x16 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5701 x16 x36 x67
  exact (fun hh => u0 (hh (And.intro u2 u1))) h

theorem clause13130 (t x01 x03 x06 x13 x34 x36 x56 x67 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + ((-1) * x36) + x56) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x06)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
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
  have u3 : ((x01 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x36) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x01 + ((-1) * x06)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th5708 t x01 x03 x06 x13 x34 x36 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u3 (And.intro u6 (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u0 (And.intro u8 u2)))))))))) h

theorem clause13131 (t x03 x13 x14 x34 x35 x36 x45 x56 x58 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x14 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((t + x03 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x56) + x58) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x03 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x35 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x56) + x58) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th5709 t x03 x13 x14 x34 x35 x36 x45 x56 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u7 (And.intro u1 (And.intro u3 (And.intro u0 (And.intro u9 (And.intro u8 (And.intro u6 (And.intro u5 u2))))))))))) h

theorem clause13132 (t x13 x35 x36 x56 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((t + ((-1) * x56) + x58) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x56) + x58) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5710 t x13 x35 x36 x56 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u3 u4))))))) h

theorem clause13133 (x36 x46 x56 : ℝ) : ((¬ ((x46 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((x36 + ((-1) * x46)) ≤ 0)) ∨ ((x36 + ((-1) * x56)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x46 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x36 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x36 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5711 x36 x46 x56
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause13135 (t x13 x34 x36 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((t + x45 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x45 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5713 t x13 x34 x36 x45 x46
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 (And.intro u3 (And.intro u0 (And.intro u5 u4)))))) h

theorem clause13136 (t x01 x06 x14 x45 x58 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((t + x01 + ((-1) * x06)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x58)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x58) + x78) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x01 + ((-1) * x06)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x58) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5714 t x01 x06 x14 x45 x58 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u7 (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u4 u6))))))))) h

theorem clause13137 (t x01 x03 x35 x45 x56 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x45 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1))) ∨ (¬ (x01 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5715 t x01 x03 x35 x45 x56 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u5 (And.intro u7 (And.intro u0 (And.intro u2 (And.intro u6 u1))))))))) h

theorem clause13138 (t x34 x45 x46 x56 x58 : ℝ) : ((¬ ((x46 + ((-1) * x56)) ≤ 0)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + ((-1) * x56) + x58) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x58)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x46 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x56) + x58) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5718 t x34 x45 x46 x56 x58
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u4 u1)))))) h

theorem clause13139 (t x34 x35 x45 x46 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((t + x45 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x45 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5719 t x34 x35 x45 x46 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u4 u5))))))) h

theorem clause13140 (t x03 x06 x13 x15 x35 x36 x45 x56 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x03 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x36)) ≤ 0)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x15 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x03 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x15 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th5722 t x03 x06 x13 x15 x35 x36 x45 x56 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u6 (And.intro u0 (And.intro u11 (And.intro u10 (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u2 (And.intro u7 (And.intro u8 u9))))))))))))) h

theorem clause13141 (t x06 x13 x35 x36 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x36)) ≤ 0)) ∨ ((t + ((-1) * x35)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5723 t x06 x13 x35 x36 x67 x78
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u4 (And.intro u2 (And.intro u5 (And.intro u3 (And.intro u6 (And.intro u0 u7)))))))) h

theorem clause13142 (x45 x56 x57 : ℝ) : ((¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x57)) ≥ 0)) ∨ ((x45 + ((-1) * x57)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x45 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5724 x45 x56 x57
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause13143 (t x05 x15 x56 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x57 + ((-1) * x67)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x15)) ≤ 0) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x57 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x15)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5725 t x05 x15 x56 x57 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u7 (And.intro u6 (And.intro u2 (And.intro u4 (And.intro u1 (And.intro u0 u5))))))))) h

theorem clause13144 (t x01 x03 x05 x13 x34 x36 x56 x67 x78 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ ((t + ((-1) * x36)) ≤ 0) ∨ (¬ ((t + x01 + ((-1) * x05)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x01 + ((-1) * x05)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th5726 t x01 x03 x05 x13 x34 x36 x56 x67 x78
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u2 (And.intro u6 (And.intro u4 (And.intro u3 (And.intro u8 (And.intro u1 (And.intro u0 (And.intro u9 (And.intro u10 u7))))))))))) h

theorem clause13145 (t x13 x34 x35 x45 x48 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x45) + x48) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x48)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x45) + x48) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5728 t x13 x34 x35 x45 x48
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u3 u2))))))) h

theorem clause13146 (t x01 x02 x03 x13 x26 x34 x36 x67 x78 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ ((t + ((-1) * x36)) ≤ 0) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
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
  have u3 : ((x01 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th5729 t x01 x02 x03 x13 x26 x34 x36 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u1 (And.intro u0 (And.intro u8 (And.intro u2 (And.intro u3 (And.intro u9 (And.intro u4 (And.intro u6 (And.intro u10 u5)))))))))))) h

theorem clause13148 (t x01 x06 x12 x15 x24 x48 x56 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x15)) ≤ 0) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((t + ((-1) * x48) + x78) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x48)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x15)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x48) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x24 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th5735 t x01 x06 x12 x15 x24 x48 x56 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u5 (And.intro u8 (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u7 (And.intro u9 (And.intro u1 (And.intro u3 u10)))))))))))) h

theorem clause13150 (t x07 x12 x24 x27 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x47 ≥ 0)) ∨ ((t + ((-1) * x24)) ≤ 0) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x27)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x47 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x07 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x07 + ((-1) * x27)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5741 t x07 x12 x24 x27 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u1 (And.intro u3 (And.intro u5 (And.intro u7 (And.intro u6 u0))))))))) h

theorem clause13152 (t x02 x07 x12 x27 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x02 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x02 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x07)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5746 t x02 x07 x12 x27 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u3 (And.intro u4 u0))))))) h

theorem clause13155 (t x03 x12 x23 x27 x36 x37 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ (x36 ≥ 0)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x27 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5750 t x03 x12 x23 x27 x36 x37
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u3 (And.intro u5 (And.intro u7 (And.intro u4 (And.intro u0 (And.intro u2 u1))))))))) h

theorem clause13157 (t x04 x12 x13 x23 x26 x27 x34 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((t + ((-1) * x23) + x26) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + ((-1) * x27) + x57) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x23) + x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x27) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th5752 t x04 x12 x13 x23 x26 x27 x34 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u6 (And.intro u3 (And.intro u8 (And.intro u9 u7))))))))))) h

theorem clause13158 (t x03 x04 x13 x34 x35 x36 x45 x56 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ ((t + ((-1) * x13)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ (x36 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + x56 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x36 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + x56 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x35 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th5755 t x03 x04 x13 x34 x35 x36 x45 x56 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u8 (And.intro u4 (And.intro u7 (And.intro u10 (And.intro u5 (And.intro u3 u9)))))))))))) h

theorem clause13159 (t x04 x13 x23 x26 x34 x45 x58 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((t + x58 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((t + ((-1) * x23) + x26) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x58 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x23) + x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th5757 t x04 x13 x23 x26 x34 x45 x58 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u3 (And.intro u6 (And.intro u1 (And.intro u0 (And.intro u8 (And.intro u2 (And.intro u9 (And.intro u5 u7))))))))))) h

theorem clause13160 (t x01 x04 x12 x27 x45 x58 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x04)) ≥ 1)) ∨ (¬ ((t + x58 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1)))) := by
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
  have u3 : ((t + x01 + ((-1) * x04)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x58 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x27 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5759 t x01 x04 x12 x27 x45 x58 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u4 (And.intro u2 (And.intro u5 (And.intro u7 (And.intro u6 u1))))))))) h

theorem clause13161 (x15 x35 x57 : ℝ) : ((¬ ((x15 + ((-1) * x35)) ≥ 0)) ∨ ((x35 + ((-1) * x57)) ≤ (-1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x15 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5764 x15 x35 x57
  exact (fun hh => u1 (hh (And.intro u0 u2))) h

theorem clause13162 (t x02 x12 x24 x26 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5766 t x02 x12 x24 x26 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u3 (And.intro u2 (And.intro u4 (And.intro u1 u6)))))))) h

theorem clause13163 (x15 x56 x57 : ℝ) : ((¬ ((x56 + ((-1) * x57)) ≥ 0)) ∨ ((x15 + ((-1) * x56)) ≤ (-1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x56 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5767 x15 x56 x57
  exact (fun hh => u1 (hh (And.intro u0 u2))) h

theorem clause13165 (t x14 x17 x45 x46 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x45 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x17)) ≥ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x47)) ≤ 0)) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x45 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x17)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x47)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5773 t x14 x17 x45 x46 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u6 u4)))))))) h

theorem clause13166 (t x16 x17 x46 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x16) + x46) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x17)) ≥ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x16) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 + ((-1) * x17)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5775 t x16 x17 x46 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u4 u3))))))) h

theorem clause13167 (t x04 x13 x34 x36 x46 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((t + x46 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x46 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5776 t x04 x13 x34 x36 x46 x56
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u1 (And.intro u2 (And.intro u4 (And.intro u5 (And.intro u3 u0))))))) h

theorem clause13168 (t x03 x04 x13 x34 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + x03 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x03 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5779 t x03 x04 x13 x34 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u5 u4))))))) h

theorem clause13170 (t x06 x45 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x06 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ (x67 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5783 t x06 x45 x56 x67 x68
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u6 (And.intro u3 u5))))))) h

theorem clause13171 (t x03 x06 x13 x15 x35 x36 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x03 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + x67 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x03 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x67 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x15 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th5784 t x03 x06 x13 x15 x35 x36 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u8 (And.intro u7 (And.intro u9 (And.intro u4 (And.intro u3 (And.intro u6 u5))))))))))) h

theorem clause13172 (t x03 x06 x13 x15 x35 x36 x57 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x03 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + x68 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x03 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + x68 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th5785 t x03 x06 x13 x15 x35 x36 x57 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u7 (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u6 (And.intro u9 (And.intro u5 (And.intro u1 u4))))))))))) h

theorem clause13173 (t x03 x04 x13 x15 x17 x34 x35 x47 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + x03 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((t + x47 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x17)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x03 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x34)) ≤ 0) := by
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
  have u7 : ((x15 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + x47 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x15 + ((-1) * x17)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th5788 t x03 x04 x13 x15 x17 x34 x35 x47 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u9 (And.intro u10 (And.intro u5 (And.intro u6 (And.intro u3 (And.intro u7 (And.intro u1 (And.intro u8 (And.intro u4 (And.intro u0 u2)))))))))))) h

theorem clause13174 (t x01 x12 x24 x45 x47 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x47) + x67) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x47) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th5797 t x01 x12 x24 x45 x47 x57 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u9 (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u2 (And.intro u8 (And.intro u0 (And.intro u5 u7))))))))))) h

theorem clause13175 (t x01 x14 x24 x45 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5798 t x01 x14 x24 x45 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u5 (And.intro u1 (And.intro u6 u2)))))))) h

theorem clause13176 (t x04 x24 x45 x46 x56 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ (x45 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5799 t x04 x24 x45 x46 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u7 (And.intro u6 (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u1 u5))))))))) h

theorem clause13177 (t x03 x13 x15 x35 x36 x37 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x03 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x36 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x03 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x57) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th5802 t x03 x13 x15 x35 x36 x37 x57 x67 x78
  exact (fun hh => (fun hh => hh u7) (hh (And.intro u8 (And.intro u5 (And.intro u3 (And.intro u1 (And.intro u9 (And.intro u0 (And.intro u6 (And.intro u2 u4)))))))))) h

theorem clause13178 (t x03 x13 x15 x35 x37 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x03 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x03 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x57) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th5803 t x03 x13 x15 x35 x37 x57 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u7 (And.intro u3 (And.intro u8 (And.intro u5 (And.intro u6 u2)))))))))) h

theorem clause13179 (t x01 x04 x15 x46 x57 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x04)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ ((t + x68 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x01 + ((-1) * x04)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x68 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5805 t x01 x04 x15 x46 x57 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u6 (And.intro u4 (And.intro u5 (And.intro u1 (And.intro u2 u7))))))))) h

theorem clause13180 (t x15 x45 x56 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ (x45 ≥ 0)) ∨ ((t + ((-1) * x78)) ≤ 0)) := by
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
  have u3 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5815 t x15 x45 x56 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u6 (And.intro u0 (And.intro u4 (And.intro u1 (And.intro u2 u5)))))))) h

theorem clause13181 (t x04 x13 x14 x34 x36 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + ((-1) * x34) + x36) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x34) + x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5818 t x04 x13 x14 x34 x36 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u5 (And.intro u6 (And.intro u0 (And.intro u4 u2)))))))) h

theorem clause13182 (t x02 x03 x23 x26 x34 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((t + ((-1) * x23) + x26) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x23) + x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5820 t x02 x03 x23 x26 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u4 u5))))))) h

theorem clause13183 (t x01 x02 x14 x26 x45 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
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
  have u7 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5821 t x01 x02 x14 x26 x45 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u7 (And.intro u1 (And.intro u0 (And.intro u5 (And.intro u3 (And.intro u4 u2))))))))) h

theorem clause13184 (t x01 x14 x24 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ (x46 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0)) := by
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
  have u3 : (x46 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5822 t x01 x14 x24 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u6 (And.intro u2 u1)))))))) h

theorem clause13185 (t x03 x12 x23 x26 x34 x36 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((t + ((-1) * x34) + x36) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x34) + x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5824 t x03 x12 x23 x26 x34 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u4 u6)))))))) h

theorem clause13186 (t x02 x06 x12 x14 x24 x26 x45 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x12) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x02) + x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x06 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th5825 t x02 x06 x12 x14 x24 x26 x45 x57 x67
  exact (fun hh => (fun hh => hh u9) (hh (And.intro u0 (And.intro u7 (And.intro u1 (And.intro u4 (And.intro u3 (And.intro u6 (And.intro u2 (And.intro u8 u5)))))))))) h

theorem clause13187 (x12 x24 x25 : ℝ) : ((¬ ((x24 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ ((x12 + ((-1) * x25)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x24 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x12 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5830 x12 x24 x25
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause13188 (t x12 x13 x23 x26 x34 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + ((-1) * x23) + x26) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x23) + x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5836 t x12 x13 x23 x26 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u3 u1))))))) h

theorem clause13189 (x04 x24 x45 : ℝ) : ((¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x24)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5839 x04 x24 x45
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 u0))) h

theorem clause13190 (x27 x47 x78 : ℝ) : ((¬ ((x47 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x47)) ≥ 0)) ∨ ((x27 + ((-1) * x78)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x27 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x27 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5844 x27 x47 x78
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause13191 (t x01 x04 x12 x14 x16 x26 x45 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x26)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x16 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th5846 t x01 x04 x12 x14 x16 x26 x45 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u7 (And.intro u0 (And.intro u6 (And.intro u8 (And.intro u9 (And.intro u3 (And.intro u5 u4))))))))))) h

theorem clause13192 (x26 x67 x68 : ℝ) : ((¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ ((x26 + ((-1) * x68)) ≥ 1) ∨ (¬ ((x67 + ((-1) * x68)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x67 + ((-1) * x68)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5847 x26 x67 x68
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause13193 (t x01 x12 x13 x23 x34 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ (x12 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5848 t x01 x12 x13 x23 x34
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u5 (And.intro u6 u4))))))) h

theorem clause13194 (t x03 x34 x36 x46 x67 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x46 ≥ 0)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x46 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5853 t x03 x34 x36 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u5 u6)))))))) h

theorem clause13195 (t x02 x12 x14 x24 x26 x45 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x12) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x02) + x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th5854 t x02 x12 x14 x24 x26 x45 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u7 (And.intro u6 (And.intro u3 (And.intro u1 (And.intro u4 u8)))))))))) h

theorem clause13196 (t x01 x06 x14 x26 x45 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x06) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + ((-1) * x26) + x56) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x01) + x06) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x26) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5855 t x01 x06 x14 x26 x45 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u7 (And.intro u2 (And.intro u5 u3))))))))) h

theorem clause13197 (t x06 x13 x16 x34 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x34) + x36) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x16)) ≥ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x34) + x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5857 t x06 x13 x16 x34 x36 x67
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u4 (And.intro u5 u1))))))) h

theorem clause13198 (x13 x23 x34 : ℝ) : ((¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5859 x13 x23 x34
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u0 u1))) h

theorem clause13200 (t x01 x02 x16 x23 x36 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + x67 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x68)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x67 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x16 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5862 t x01 x02 x16 x23 x36 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u2 (And.intro u0 (And.intro u7 (And.intro u3 (And.intro u1 (And.intro u4 u5))))))))) h

theorem clause13201 (t x02 x06 x13 x16 x23 x34 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ (x02 ≥ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x16)) ≥ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x13 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th5867 t x02 x06 x13 x16 x23 x34 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u6 (And.intro u8 (And.intro u5 (And.intro u2 (And.intro u3 (And.intro u1 u7)))))))))) h

theorem clause13203 (t x01 x02 x16 x24 x46 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + x67 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x68)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x67 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x16 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5871 t x01 x02 x16 x24 x46 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u1 (And.intro u0 (And.intro u6 (And.intro u5 u7))))))))) h

theorem clause13204 (t x01 x04 x12 x13 x14 x34 x45 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x67 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th5872 t x01 x04 x12 x13 x14 x34 x45 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u0 (And.intro u8 (And.intro u10 (And.intro u1 (And.intro u2 (And.intro u3 (And.intro u9 (And.intro u7 u6)))))))))))) h

theorem clause13205 (t x03 x13 x23 x34 x36 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ (x13 ≥ 0)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5873 t x03 x13 x23 x34 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u6 (And.intro u0 (And.intro u5 (And.intro u1 u4)))))))) h

theorem clause13206 (t x01 x03 x13 x14 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x13 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x13 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5875 t x01 x03 x13 x14 x36
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u3 (And.intro u5 (And.intro u2 (And.intro u1 u0)))))) h

theorem clause13207 (t x03 x14 x34 x36 x46 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + x14 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + x14 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5878 t x03 x14 x34 x36 x46
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u1 (And.intro u5 (And.intro u3 (And.intro u0 u2)))))) h

theorem clause13208 (t x03 x24 x34 x36 x46 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + x24 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + x24 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5881 t x03 x24 x34 x36 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u2 u3))))))) h

theorem clause13209 (t x01 x03 x12 x13 x25 x36 x37 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((t + ((-1) * x37) + x57) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x37) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th5884 t x01 x03 x12 x13 x25 x36 x37 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u9 (And.intro u0 (And.intro u4 (And.intro u7 (And.intro u6 (And.intro u5 (And.intro u2 (And.intro u8 u3))))))))))) h

theorem clause13210 (t x01 x04 x14 x45 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ (x78 ≥ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5886 t x01 x04 x14 x45 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u4 (And.intro u6 (And.intro u7 (And.intro u5 u0))))))))) h

theorem clause13211 (t x03 x07 x13 x37 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x03) + x13) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x07)) ≥ 0)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x03) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x07 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x07)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5889 t x03 x07 x13 x37 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u4 u5))))))) h

theorem clause13212 (t x01 x04 x14 x45 x46 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ (x68 ≥ 0)) ∨ ((t + ((-1) * x01)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x68 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5894 t x01 x04 x14 x45 x46 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u1 (And.intro u5 (And.intro u3 (And.intro u4 (And.intro u0 (And.intro u2 u6))))))))) h

theorem clause13213 (t x01 x02 x04 x14 x26 x45 x47 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x47 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x47 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th5897 t x01 x02 x04 x14 x26 x45 x47 x67
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u1 (And.intro u3 (And.intro u7 (And.intro u8 (And.intro u6 (And.intro u5 (And.intro u0 u2))))))))) h

theorem clause13214 (t x03 x14 x34 x37 x46 x47 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ (x46 ≥ 0)) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x47)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x37 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5898 t x03 x14 x34 x37 x46 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u0 (And.intro u6 (And.intro u1 (And.intro u2 (And.intro u4 u7))))))))) h

theorem clause13215 (t x03 x13 x36 x37 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5899 t x03 x13 x36 x37 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u6 (And.intro u3 u5)))))))) h

theorem clause13216 (t x01 x03 x04 x13 x17 x36 x37 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x04)) ≥ 0)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((t + x17 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x17 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th5900 t x01 x03 x04 x13 x17 x36 x37 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u1 (And.intro u6 (And.intro u9 (And.intro u5 (And.intro u2 (And.intro u7 (And.intro u8 (And.intro u3 u10)))))))))))) h

theorem clause13219 (t x01 x03 x12 x24 x36 x47 x67 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((t + x47 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x47 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5908 t x01 x03 x12 x24 x36 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u2 (And.intro u1 (And.intro u4 (And.intro u3 (And.intro u5 (And.intro u6 u0))))))))) h

theorem clause13220 (t x01 x03 x12 x27 x35 x56 x67 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + x27 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≥ 1) := by
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
  have u6 : ((t + x27 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5909 t x01 x03 x12 x27 x35 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u6 (And.intro u3 (And.intro u7 (And.intro u2 (And.intro u1 (And.intro u0 u5))))))))) h

theorem clause13221 (t x05 x24 x34 x35 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((t + x24 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x24 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5910 t x05 x24 x34 x35 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u6 (And.intro u1 (And.intro u4 (And.intro u3 (And.intro u0 u5)))))))) h

theorem clause13222 (t x04 x24 x25 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + ((-1) * x04) + x24) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x04) + x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5911 t x04 x24 x25 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u1 (And.intro u5 (And.intro u3 u2))))))) h

theorem clause13224 (t x05 x24 x34 x35 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((t + x24 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x24 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5914 t x05 x24 x34 x35 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u3 (And.intro u4 (And.intro u5 (And.intro u0 (And.intro u2 u1)))))))) h

theorem clause13225 (x17 x27 x78 : ℝ) : ((¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x27)) ≥ 0)) ∨ ((x27 + ((-1) * x78)) ≤ (-1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x17 + ((-1) * x27)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x27 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5915 x17 x27 x78
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause13226 (t x01 x03 x12 x17 x27 x35 x57 x78 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + x27 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x17)) ≥ 0)) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x27 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x17)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x27 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th5919 t x01 x03 x12 x17 x27 x35 x57 x78
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u7 (And.intro u8 (And.intro u1 (And.intro u3 (And.intro u4 (And.intro u0 (And.intro u2 u6))))))))) h

theorem clause13227 (t x01 x03 x12 x27 x35 x58 x78 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x58) + x78) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x58) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5929 t x01 x03 x12 x27 x35 x58 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u5 (And.intro u7 (And.intro u2 (And.intro u1 (And.intro u4 (And.intro u0 u3))))))))) h

theorem clause13228 (t x01 x03 x12 x26 x35 x36 x56 x67 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + x26 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x26 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th5931 t x01 x03 x12 x26 x35 x36 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u7 (And.intro u8 (And.intro u6 (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u3 u5)))))))))) h

theorem clause13229 (t x02 x04 x06 x24 x36 x46 x47 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((t + ((-1) * x36) + x46) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x02) + x06) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1))) := by
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
  have u3 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x36) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x02) + x06) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th5934 t x02 x04 x06 x24 x36 x46 x47 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u8 (And.intro u6 (And.intro u7 (And.intro u5 (And.intro u1 (And.intro u2 u0)))))))))) h

theorem clause13230 (x14 x24 x47 : ℝ) : (((x14 + ((-1) * x47)) ≥ 1) ∨ (¬ ((x14 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5936 x14 x24 x47
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause13231 (t x34 x45 x46 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x45 ≥ 0)) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5943 t x34 x45 x46 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u4 (And.intro u0 (And.intro u5 u6)))))))) h

theorem clause13232 (t x01 x03 x12 x25 x35 x56 x57 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≥ 1) := by
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
  have u5 : ((t + ((-1) * x56) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5945 t x01 x03 x12 x25 x35 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u3 (And.intro u1 (And.intro u0 (And.intro u4 (And.intro u7 (And.intro u2 u5))))))))) h

theorem clause13233 (t x01 x12 x25 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ (¬ (x67 ≥ 0)) ∨ ((t + ((-1) * x01)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5947 t x01 x12 x25 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u1 (And.intro u6 (And.intro u2 (And.intro u3 u4)))))))) h

theorem clause13234 (x12 x25 x26 : ℝ) : ((¬ ((x25 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ ((x12 + ((-1) * x26)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x25 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x12 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5949 x12 x25 x26
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause13235 (t x01 x12 x26 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5950 t x01 x12 x26 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u6 (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u1 u2)))))))) h

theorem clause13236 (t x04 x06 x24 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x04) + x24) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x06)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x04) + x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5956 t x04 x06 x24 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u3 (And.intro u1 (And.intro u0 u4))))))) h

theorem clause13237 (t x04 x24 x26 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x04) + x24) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x26)) ≤ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x04) + x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5957 t x04 x24 x26 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u4 (And.intro u2 (And.intro u1 u0))))))) h

theorem clause13238 (t x01 x03 x12 x25 x37 x58 x78 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((t + x58 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x58 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5960 t x01 x03 x12 x25 x37 x58 x78
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u4 (And.intro u5 (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u7 u3)))))))) h

theorem clause13240 (t x01 x02 x03 x12 x26 x27 x35 x57 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + x27 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x02)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x27 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th5965 t x01 x02 x03 x12 x26 x27 x35 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u6 (And.intro u7 (And.intro u4 (And.intro u2 (And.intro u1 (And.intro u3 u8)))))))))) h

theorem clause13241 (t x01 x03 x12 x26 x35 x57 x67 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x57) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th5966 t x01 x03 x12 x26 x35 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u6 (And.intro u5 (And.intro u7 (And.intro u4 (And.intro u1 u3))))))))) h

theorem clause13242 (t x01 x15 x45 : ℝ) : (((t + ((-1) * x15) + x45) ≥ 1) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x15) + x45) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th5972 t x01 x15 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u0 u1))))) h

theorem clause13243 (t x03 x24 x34 x35 x45 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((t + x24 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1)))) := by
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
  have u3 : ((x35 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x24 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5973 t x03 x24 x34 x35 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u5 (And.intro u1 (And.intro u0 u2))))))) h

theorem clause13244 (t x35 x45 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x35) + x45) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x35) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5974 t x35 x45 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u0 u5))))))) h

theorem clause13245 (t x02 x12 x14 x24 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x12) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x02) + x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≥ 1) := by
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
  have h := NineTheoryTrial.th5976 t x02 x12 x14 x24 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u3 u4))))))) h

theorem clause13246 (t x02 x23 x24 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ (x57 ≥ 0))) := by
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
  have u4 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x57 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5977 t x02 x23 x24 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u4 (And.intro u5 (And.intro u6 (And.intro u1 u2)))))))) h

theorem clause13247 (t x02 x24 x26 x45 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x45 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5982 t x02 x24 x26 x45 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u0 (And.intro u4 (And.intro u1 (And.intro u2 u6)))))))) h

theorem clause13248 (t x06 x26 x56 : ℝ) : (((t + x06 + ((-1) * x56)) ≥ 1) ∨ (¬ ((x06 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((t + x26 + ((-1) * x56)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x06 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x06 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x26 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5983 t x06 x26 x56
  exact (fun hh => u0 (hh (And.intro u2 u1))) h

theorem clause13249 (x02 x24 x25 : ℝ) : (((x02 + ((-1) * x25)) ≥ 1) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x25)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5984 x02 x24 x25
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause13250 (t x01 x13 x35 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ ((t + ((-1) * x01)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x13)) ≥ 1) := by
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
  have u6 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th5986 t x01 x13 x35 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u6 (And.intro u3 u1)))))))) h

theorem clause13251 (t x15 x35 x45 : ℝ) : ((¬ ((t + ((-1) * x35) + x45) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x45)) ≥ 0)) ∨ ((t + x15 + ((-1) * x35)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x35) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x15 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + x15 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th5994 t x15 x35 x45
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause13252 (t x03 x12 x23 x25 x35 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((t + ((-1) * x03) + x23) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x25 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x03) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th5998 t x03 x12 x23 x25 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u3 (And.intro u0 (And.intro u2 u5))))))) h

theorem clause13253 (t x01 x02 x16 x23 x35 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6000 t x01 x02 x16 x23 x35 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u7 (And.intro u3 (And.intro u6 (And.intro u5 (And.intro u0 u4))))))))) h

theorem clause13254 (t x01 x02 x16 x23 x35 x56 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
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
  have u4 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6003 t x01 x02 x16 x23 x35 x56 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u8 (And.intro u0 (And.intro u4 (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u9 (And.intro u6 u7))))))))))) h

theorem clause13255 (t x02 x03 x06 x24 x36 x45 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x03) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((t + ((-1) * x36) + x56) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x02) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x36) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6005 t x02 x03 x06 x24 x36 x45 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u7 (And.intro u4 (And.intro u5 (And.intro u6 (And.intro u3 (And.intro u8 u2)))))))))) h

theorem clause13256 (t x02 x24 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6007 t x02 x24 x46 x56 x67
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u6 u4))))))) h

theorem clause13257 (x25 x45 x57 : ℝ) : ((¬ ((x25 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ ((x25 + ((-1) * x57)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x25 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x25 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6011 x25 x45 x57
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause13258 (t x02 x12 x14 x24 x25 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x12) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x02) + x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x56) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6012 t x02 x12 x14 x24 x25 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u6 (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u8 u7)))))))))) h

theorem clause13259 (t x02 x12 x24 x25 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1)) ∨ (¬ (x57 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x57 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6013 t x02 x12 x24 x25 x57
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u2 (And.intro u1 (And.intro u5 (And.intro u0 (And.intro u3 u6))))))) h

theorem clause13260 (t x01 x12 x14 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ (x57 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x57 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6015 t x01 x12 x14 x45 x57
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u1 (And.intro u2 (And.intro u4 (And.intro u6 (And.intro u0 u5))))))) h

theorem clause13261 (t x03 x05 x23 x35 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x03) + x23) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x05)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x03) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6017 t x03 x05 x23 x35 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u1 u3))))))) h

theorem clause13262 (t x03 x14 x34 x36 x46 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x14) + x34) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x14) + x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6019 t x03 x14 x34 x36 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u3 (And.intro u0 (And.intro u2 u5))))))) h

theorem clause13263 (t x13 x17 x34 x37 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x17)) ≥ 0)) ∨ (¬ ((t + ((-1) * x34) + x37) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x17)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x34) + x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6021 t x13 x17 x34 x37 x78
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u5 u3)))))) h

theorem clause13266 (t x01 x04 x12 x14 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6028 t x01 x04 x12 x14 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u5 u2))))))) h

theorem clause13267 (t x13 x15 x23 x35 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x13 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x15)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x13 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6029 t x13 x15 x23 x35 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u4 (And.intro u5 u2))))))) h

theorem clause13268 (t x01 x03 x12 x13 x14 x35 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6032 t x01 x03 x12 x13 x14 x35
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u2 (And.intro u6 (And.intro u5 (And.intro u1 (And.intro u3 u4))))))) h

theorem clause13270 (t x12 x25 x35 x56 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x35 + ((-1) * x58)) ≥ 1)) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6036 t x12 x25 x35 x56 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u1 (And.intro u6 (And.intro u3 (And.intro u4 u5)))))))) h

theorem clause13271 (t x01 x02 x03 x12 x14 x15 x23 x34 x36 x56 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x03)) ≤ 0)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th6037 t x01 x02 x03 x12 x14 x15 x23 x34 x36 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u1 (And.intro u11 (And.intro u8 (And.intro u10 (And.intro u2 (And.intro u5 (And.intro u3 (And.intro u9 (And.intro u4 (And.intro u0 u7))))))))))))) h

theorem clause13272 (t x01 x02 x12 x14 x15 x23 x36 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x36) + x56) ≥ 1)) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x36) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6038 t x01 x02 x12 x14 x15 x23 x36 x56
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u3 (And.intro u8 (And.intro u4 (And.intro u5 (And.intro u1 (And.intro u7 (And.intro u2 u0))))))))) h

theorem clause13273 (t x01 x05 x12 x14 x15 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x15)) ≤ 0))) := by
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
  have u3 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6039 t x01 x05 x12 x14 x15 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u2 u1)))))))) h

theorem clause13277 (t x01 x07 x12 x14 x17 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x17)) ≤ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x07)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x17)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x07 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x07)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6046 t x01 x07 x12 x14 x17 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u1 (And.intro u3 (And.intro u4 (And.intro u0 (And.intro u5 u2)))))))) h

theorem clause13278 (t x01 x03 x12 x13 x14 x17 x35 x37 x47 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x47)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x37)) ≤ 0)) ∨ (¬ ((t + x47 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x17 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x35 + ((-1) * x37)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + x47 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th6047 t x01 x03 x12 x13 x14 x17 x35 x37 x47 x57 x78
  exact (fun hh => (fun hh => hh u11) (hh (And.intro u3 (And.intro u10 (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u8 (And.intro u2 (And.intro u6 (And.intro u0 (And.intro u9 u7)))))))))))) h

theorem clause13279 (t x13 x17 x23 x37 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x13 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x17)) ≤ 0)) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x13 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x17)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6048 t x13 x17 x23 x37 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u4 (And.intro u3 (And.intro u1 (And.intro u5 u0))))))) h

theorem clause13281 (t x01 x03 x12 x13 x14 x17 x23 x34 x38 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ (x78 ≥ 0)) ∨ (¬ ((x23 + ((-1) * x38)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x38)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x23 + ((-1) * x38)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x03 + ((-1) * x38)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th6051 t x01 x03 x12 x13 x14 x17 x23 x34 x38 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u7 (And.intro u9 (And.intro u8 (And.intro u0 (And.intro u2 (And.intro u1 (And.intro u6 (And.intro u10 (And.intro u11 (And.intro u4 u3))))))))))))) h

theorem clause13282 (t x01 x02 x12 x14 x17 x23 x38 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + ((-1) * x38) + x78) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x38)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x38) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x23 + ((-1) * x38)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6052 t x01 x02 x12 x14 x17 x23 x38 x78
  exact (fun hh => (fun hh => hh u8) (hh (And.intro u6 (And.intro u7 (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u1 (And.intro u5 u2))))))))) h

theorem clause13283 (t x03 x05 x23 x35 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((t + x03 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x03 + ((-1) * x23)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6053 t x03 x05 x23 x35 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u5 (And.intro u0 (And.intro u2 u3))))))) h

theorem clause13285 (t x01 x12 x17 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ ((t + ((-1) * x57)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6055 t x01 x12 x17 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u3 (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u6 u2)))))))) h

theorem clause13286 (t x03 x12 x13 x17 x23 x35 x37 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x37) + x47) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((t + x12 + ((-1) * x17)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x37) + x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + x12 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6057 t x03 x12 x13 x17 x23 x35 x37 x47 x78
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u9 (And.intro u8 (And.intro u6 (And.intro u7 (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u1 u4)))))))))) h

theorem clause13287 (t x02 x12 x17 x23 x35 x47 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + x47 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((t + x12 + ((-1) * x17)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x47 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x12 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6058 t x02 x12 x17 x23 x35 x47 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u4 (And.intro u6 (And.intro u5 (And.intro u8 (And.intro u0 (And.intro u3 (And.intro u7 u1)))))))))) h

theorem clause13288 (t x02 x04 x12 x14 x23 x36 x47 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x68) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6059 t x02 x04 x12 x14 x23 x36 x47 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u4 (And.intro u9 (And.intro u6 (And.intro u0 (And.intro u3 (And.intro u8 (And.intro u7 u2))))))))))) h

theorem clause13289 (t x02 x04 x12 x14 : ℝ) : ((¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ ((t + x02 + ((-1) * x04)) ≥ 1) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + x02 + ((-1) * x04)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th6063 t x02 x04 x12 x14
  exact (fun hh => u1 (hh (And.intro u2 (And.intro u3 u0)))) h

theorem clause13292 (t x01 x02 x12 x14 x16 x26 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x16 + ((-1) * x56)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x67)) ≥ 1) := by
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
  have u8 : ((t + x16 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6068 t x01 x02 x12 x14 x16 x26 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u6 (And.intro u3 (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u4 (And.intro u8 u7)))))))))) h

theorem clause13293 (t x01 x02 x03 x12 x14 x16 x23 x35 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((t + x16 + ((-1) * x36)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + x16 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6071 t x01 x02 x03 x12 x14 x16 x23 x35 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u4 (And.intro u7 (And.intro u6 (And.intro u9 u8))))))))))) h

theorem clause13294 (t x02 x03 x36 x56 x67 x68 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x02 ≥ 0)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6072 t x02 x03 x36 x56 x67 x68
  exact (fun hh => (fun hh => hh u7) (hh (And.intro u4 (And.intro u0 (And.intro u6 (And.intro u5 (And.intro u3 (And.intro u2 u1)))))))) h

theorem clause13295 (t x16 x23 x34 x36 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x68)) ≤ (-1))) ∨ (¬ (x16 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x16 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6073 t x16 x23 x34 x36 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u6 (And.intro u4 (And.intro u5 (And.intro u2 (And.intro u1 u3)))))))) h

theorem clause13296 (t x02 x04 x25 x47 x56 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((t + x02 + ((-1) * x04)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x02 + ((-1) * x04)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x68) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6074 t x02 x04 x25 x47 x56 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u3 (And.intro u0 (And.intro u6 (And.intro u2 (And.intro u4 u7))))))))) h

theorem clause13297 (t x02 x03 x12 x14 x16 x23 x35 x36 x46 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x16)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ ((t + ((-1) * x36)) ≤ 0) ∨ (¬ (x67 ≥ 0)) ∨ (¬ ((x16 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x14 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ¬ ((t + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))))
  have u12 : ((x16 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))))
  have h := NineTheoryTrial.th6079 t x02 x03 x12 x14 x16 x23 x35 x36 x46 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u10 (And.intro u9 (And.intro u0 (And.intro u4 (And.intro u1 (And.intro u3 (And.intro u12 (And.intro u7 (And.intro u6 (And.intro u11 (And.intro u5 u8)))))))))))))) h

theorem clause13299 (t x02 x03 x04 x12 x14 x23 x35 x37 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((t + ((-1) * x37) + x67) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
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
  have u7 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((t + ((-1) * x37) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th6082 t x02 x03 x04 x12 x14 x23 x35 x37 x46 x67
  exact (fun hh => (fun hh => hh u8) (hh (And.intro u1 (And.intro u9 (And.intro u5 (And.intro u7 (And.intro u4 (And.intro u2 (And.intro u6 (And.intro u10 (And.intro u0 u3))))))))))) h

theorem clause13300 (t x03 x23 x35 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x03 ≥ 0)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x03 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6083 t x03 x23 x35 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u6 (And.intro u2 (And.intro u4 u3)))))))) h

theorem clause13301 (t x02 x03 x06 x23 x35 x36 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x36) + x46) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((t + x02 + ((-1) * x06)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x36) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x02 + ((-1) * x06)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6084 t x02 x03 x06 x23 x35 x36 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u4 (And.intro u5 (And.intro u7 (And.intro u8 (And.intro u6 u0)))))))))) h

theorem clause13302 (t x01 x02 x12 x14 x17 x23 x35 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + x17 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x17 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6087 t x01 x02 x12 x14 x17 x23 x35 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u8 (And.intro u2 (And.intro u3 (And.intro u5 (And.intro u6 (And.intro u7 u1)))))))))) h

theorem clause13303 (t x02 x04 x23 x35 x47 x58 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((t + x02 + ((-1) * x04)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x58) + x78) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x02 + ((-1) * x04)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x58) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6088 t x02 x04 x23 x35 x47 x58 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u4 (And.intro u7 (And.intro u6 (And.intro u0 (And.intro u3 u2))))))))) h

theorem clause13304 (x12 x13 x15 : ℝ) : ((¬ ((x12 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x15)) ≤ 0)) ∨ ((x12 + ((-1) * x15)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x12 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x12 + ((-1) * x15)) ≤ 0) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6089 x12 x13 x15
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause13305 (x23 x35 x37 : ℝ) : ((¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ ((x23 + ((-1) * x37)) ≤ (-1)) ∨ (¬ ((x35 + ((-1) * x37)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x37)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6090 x23 x35 x37
  exact (fun hh => u1 (hh (And.intro u0 u2))) h

theorem clause13307 (t x03 x25 x35 x56 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x25 + ((-1) * x58)) ≥ 1)) ∨ (¬ (x03 ≥ 0)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x25 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x03 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6093 t x03 x25 x35 x56 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u6 (And.intro u5 u1)))))))) h

theorem clause13309 (t x04 x12 x14 x15 x25 x46 x57 x58 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((x25 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x15)) ≤ 0)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x57) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x15 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6098 t x04 x12 x14 x15 x25 x46 x57 x58 x67
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u8 (And.intro u4 (And.intro u9 (And.intro u3 (And.intro u7 (And.intro u0 (And.intro u6 (And.intro u5 u1)))))))))) h

theorem clause13310 (t x04 x06 x12 x14 x15 x25 x46 x56 x58 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x46 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x06)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((x25 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x15)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x46 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x12 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x15 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th6100 t x04 x06 x12 x14 x15 x25 x46 x56 x58 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u6 (And.intro u8 (And.intro u0 (And.intro u7 (And.intro u10 (And.intro u9 (And.intro u5 u4)))))))))))) h

theorem clause13312 (t x12 x25 x35 x57 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x58)) ≥ 1)) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ ((t + ((-1) * x57)) ≤ 0) ∨ (¬ ((x25 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6105 t x12 x25 x35 x57 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u6 (And.intro u0 (And.intro u2 (And.intro u1 u4)))))))) h

theorem clause13315 (t x01 x13 x17 x23 x37 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + x13 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x37)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x13 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x17 + ((-1) * x37)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6120 t x01 x13 x17 x23 x37
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u5 (And.intro u3 (And.intro u1 u2))))))) h

theorem clause13316 (t x02 x03 x04 x12 x14 x23 x36 x37 x45 x57 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((t + ((-1) * x37) + x57) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x37) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th6122 t x02 x03 x04 x12 x14 x23 x36 x37 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u6 (And.intro u0 (And.intro u8 (And.intro u5 (And.intro u1 (And.intro u7 (And.intro u9 (And.intro u10 (And.intro u3 u4)))))))))))) h

theorem clause13317 (t x01 x13 x16 x23 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + x13 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x36)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x13 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x36)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6123 t x01 x13 x16 x23 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u5 u3))))))) h

theorem clause13319 (t x01 x05 x12 x15 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + x12 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x05)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x12 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6127 t x01 x05 x12 x15 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u5 u2))))))) h

theorem clause13320 (t x01 x04 x05 x12 x14 x17 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x17) + x67) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x17) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6128 t x01 x04 x05 x12 x14 x17 x57 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u7 (And.intro u8 (And.intro u6 (And.intro u5 u9))))))))))) h

theorem clause13321 (x05 x56 x58 : ℝ) : ((¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ ((x05 + ((-1) * x58)) ≥ 1) ∨ (¬ ((x56 + ((-1) * x58)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x58)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x58)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6129 x05 x56 x58
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause13322 (t x02 x04 x05 x23 x38 x46 x56 x67 x78 : ℝ) : ((¬ ((x46 + ((-1) * x56)) ≤ 0)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((t + x02 + ((-1) * x04)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((t + ((-1) * x38) + x78) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x38)) ≤ (-1)))) := by
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
  have u3 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x02 + ((-1) * x04)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x38) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x23 + ((-1) * x38)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6132 t x02 x04 x05 x23 x38 x46 x56 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u8 (And.intro u1 (And.intro u4 (And.intro u7 (And.intro u0 (And.intro u5 (And.intro u6 (And.intro u2 u9))))))))))) h

theorem clause13323 (t x04 x05 x12 x13 x14 x23 x34 x38 x46 x56 x67 x78 : ℝ) : ((¬ ((x46 + ((-1) * x56)) ≤ 0)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x78 ≥ 0)) ∨ (¬ ((x13 + ((-1) * x38)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x38)) ≥ 1))) := by
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
  have u3 : ((x12 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))))
  have u12 : ((x13 + ((-1) * x38)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))))
  have u13 : ((x23 + ((-1) * x38)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))))
  have h := NineTheoryTrial.th6133 t x04 x05 x12 x13 x14 x23 x34 x38 x46 x56 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u4 (And.intro u3 (And.intro u6 (And.intro u11 (And.intro u10 (And.intro u0 (And.intro u1 (And.intro u7 (And.intro u2 (And.intro u13 (And.intro u9 (And.intro u12 u5))))))))))))))) h

theorem clause13324 (t x01 x02 x12 x13 x14 x23 x34 x38 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((t + ((-1) * x34) + x38) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x38)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x34) + x38) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x13 + ((-1) * x38)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6135 t x01 x02 x12 x13 x14 x23 x34 x38
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u6 (And.intro u1 (And.intro u4 (And.intro u8 (And.intro u2 (And.intro u3 u7)))))))))) h

theorem clause13325 (t x01 x04 x12 x14 x17 x46 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((t + x68 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x68 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6139 t x01 x04 x12 x14 x17 x46 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u3 (And.intro u4 (And.intro u6 (And.intro u8 (And.intro u1 (And.intro u5 (And.intro u0 u2)))))))))) h

theorem clause13326 (x46 x56 x67 : ℝ) : ((¬ ((x46 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ ((x56 + ((-1) * x67)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x46 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x56 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6140 x46 x56 x67
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause13327 (t x01 x07 x12 x17 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((t + x12 + ((-1) * x17)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x07)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x12 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6141 t x01 x07 x12 x17 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u3 (And.intro u4 u2))))))) h

theorem clause13328 (x23 x34 x35 : ℝ) : ((¬ ((x34 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ ((x23 + ((-1) * x35)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x23 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6145 x23 x34 x35
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause13329 (t x04 x05 x13 x15 x23 x34 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x13 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x15)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x13 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6148 t x04 x05 x13 x15 x23 x34 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u7 (And.intro u2 (And.intro u5 (And.intro u1 (And.intro u6 (And.intro u0 u3))))))))) h

theorem clause13330 (t x14 x23 x34 x36 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ (x45 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6168 t x14 x23 x34 x36 x45 x46
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u2 (And.intro u6 (And.intro u7 (And.intro u1 (And.intro u0 (And.intro u3 u4)))))))) h

theorem clause13331 (t x01 x02 x14 x27 x46 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + x68 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x68 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x27 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6171 t x01 x02 x14 x27 x46 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u1 (And.intro u7 (And.intro u4 (And.intro u3 (And.intro u6 u0))))))))) h

theorem clause13332 (t x05 x15 x35 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + x15 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x15 + ((-1) * x35)) ≥ 1) := by
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
  have h := NineTheoryTrial.th6175 t x05 x15 x35 x56 x57
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u3 (And.intro u5 (And.intro u0 (And.intro u2 u4)))))) h

theorem clause13334 (t x01 x03 x14 x23 x34 x37 x46 x67 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ (x67 ≥ 0)) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x23 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6183 t x01 x03 x14 x23 x34 x37 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u9 (And.intro u5 (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u8 (And.intro u6 (And.intro u7 u4))))))))))) h

theorem clause13335 (t x01 x02 x14 x23 x37 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + ((-1) * x37) + x67) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x37) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6184 t x01 x02 x14 x23 x37 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u7 (And.intro u1 (And.intro u2 (And.intro u6 (And.intro u0 u4))))))))) h

theorem clause13336 (t x01 x02 x14 x23 x36 x47 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((t + x47 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x47 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6185 t x01 x02 x14 x23 x36 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u7 (And.intro u6 (And.intro u2 (And.intro u1 (And.intro u4 u5))))))))) h

theorem clause13337 (t x01 x03 x14 x23 x34 x35 x46 x67 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ (x67 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6188 t x01 x03 x14 x23 x34 x35 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u6 (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u7 (And.intro u8 (And.intro u9 u5))))))))))) h

theorem clause13338 (t x01 x04 x12 x14 x15 x46 x56 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0)) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th6190 t x01 x04 x12 x14 x15 x46 x56 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u3 (And.intro u1 (And.intro u9 (And.intro u2 (And.intro u7 (And.intro u6 (And.intro u0 (And.intro u8 (And.intro u5 u10)))))))))))) h

theorem clause13339 (t x01 x04 x06 x12 x14 x15 x46 x56 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((t + x46 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x06)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x46 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x06 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6191 t x01 x04 x06 x12 x14 x15 x46 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u8 (And.intro u7 (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u9 (And.intro u6 u5))))))))))) h

theorem clause13340 (x16 x46 x56 : ℝ) : ((¬ ((x46 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((x16 + ((-1) * x46)) ≥ 0)) ∨ ((x16 + ((-1) * x56)) ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x46 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x16 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x16 + ((-1) * x56)) ≥ 0) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6193 x16 x46 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 u1)))) h

theorem clause13341 (t x23 x36 x38 x46 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x36) + x46) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x38 + ((-1) * x68)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x38)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x36) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x38 + ((-1) * x68)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x38)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6194 t x23 x36 x38 x46 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u2 (And.intro u0 (And.intro u3 u5))))))) h

theorem clause13342 (t x02 x04 x12 x14 x23 x38 x45 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + ((-1) * x38) + x78) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x38)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x38) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x23 + ((-1) * x38)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6195 t x02 x04 x12 x14 x23 x38 x45 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u7 (And.intro u4 (And.intro u8 (And.intro u3 (And.intro u9 (And.intro u5 (And.intro u2 (And.intro u0 u6))))))))))) h

theorem clause13343 (t x02 x04 x23 x37 x45 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((t + x02 + ((-1) * x04)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + ((-1) * x37) + x67) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x02 + ((-1) * x04)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x37) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6197 t x02 x04 x23 x37 x45 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u7 (And.intro u0 (And.intro u4 (And.intro u5 (And.intro u3 (And.intro u1 u6))))))))) h

theorem clause13344 (t x02 x04 x23 x37 x45 x58 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((t + x02 + ((-1) * x04)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((t + x58 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x02 + ((-1) * x04)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x58 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6203 t x02 x04 x23 x37 x45 x58 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u7 (And.intro u4 (And.intro u6 (And.intro u1 (And.intro u3 u2))))))))) h

theorem clause13345 (x02 x05 x15 x25 : ℝ) : ((¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x15)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x15 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x05 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th6204 x02 x05 x15 x25
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u1 u0))))) h

theorem clause13346 (t x01 x04 x12 x14 x17 x37 x47 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x37) + x57) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x37)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x37) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x17 + ((-1) * x37)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6205 t x01 x04 x12 x14 x17 x37 x47 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u3 (And.intro u9 (And.intro u1 (And.intro u8 (And.intro u0 (And.intro u7 (And.intro u5 (And.intro u6 u2))))))))))) h

theorem clause13347 (t x02 x07 x23 x36 x47 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((t + x47 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((t + x02 + ((-1) * x07)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x07 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x47 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x02 + ((-1) * x07)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6207 t x02 x07 x23 x36 x47 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u7 (And.intro u3 (And.intro u2 (And.intro u4 u6))))))))) h

theorem clause13348 (t x01 x12 x15 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≥ 0) := by
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
  have h := NineTheoryTrial.th6208 t x01 x12 x15 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u4 (And.intro u1 (And.intro u0 (And.intro u6 u3)))))))) h

theorem clause13349 (t x01 x13 x15 x23 x35 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + x13 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x13 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x35)) ≥ 1) := by
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
  have h := NineTheoryTrial.th6209 t x01 x13 x15 x23 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u5 u4))))))) h

theorem clause13350 (t x02 x04 x05 x12 x14 : ℝ) : ((¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ ((t + x02 + ((-1) * x05)) ≥ 1) ∨ (¬ ((x04 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + x02 + ((-1) * x05)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hh))))
  have h := NineTheoryTrial.th6210 t x02 x04 x05 x12 x14
  exact (fun hh => u1 (hh (And.intro u4 (And.intro u0 (And.intro u2 u3))))) h

theorem clause13352 (t x02 x05 x23 x37 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((t + x02 + ((-1) * x05)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x37) + x57) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x02 + ((-1) * x05)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x37) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6212 t x02 x05 x23 x37 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u7 (And.intro u2 (And.intro u1 (And.intro u5 (And.intro u6 u4))))))))) h

theorem clause13353 (t x01 x04 x12 x14 x15 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x56) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6213 t x01 x04 x12 x14 x15 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u0 (And.intro u6 (And.intro u8 (And.intro u7 (And.intro u3 (And.intro u2 u4)))))))))) h

theorem clause13354 (t x01 x12 x14 x24 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ ((t + ((-1) * x24)) ≤ 0) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ (x12 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x46)) ≥ 1) := by
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
  have u6 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6214 t x01 x12 x14 x24 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u6 (And.intro u3 (And.intro u1 (And.intro u0 (And.intro u4 u2)))))))) h

theorem clause13355 (t x01 x13 x14 x24 x34 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x24)) ≤ 0))) := by
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
  have u3 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x14 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6216 t x01 x13 x14 x24 x34 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u5 (And.intro u2 (And.intro u3 (And.intro u1 (And.intro u6 u7))))))))) h

theorem clause13357 (t x01 x04 x12 x14 x16 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x16) + x56) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x16) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6219 t x01 x04 x12 x14 x16 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u8 (And.intro u0 (And.intro u7 (And.intro u1 (And.intro u6 (And.intro u5 (And.intro u4 u3)))))))))) h

theorem clause13358 (t x01 x04 x12 x14 x15 x46 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x57) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6220 t x01 x04 x12 x14 x15 x46 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u3 (And.intro u8 (And.intro u6 (And.intro u2 u7)))))))))) h

theorem clause13360 (t x02 x03 x06 x23 x34 x38 x46 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x03)) ≤ 0)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ (x68 ≥ 0)) ∨ (¬ ((t + x02 + ((-1) * x06)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x38)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x38)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x68 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x02 + ((-1) * x06)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x23 + ((-1) * x38)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x03 + ((-1) * x38)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th6236 t x02 x03 x06 x23 x34 x38 x46 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u2 (And.intro u5 (And.intro u4 (And.intro u6 (And.intro u0 (And.intro u7 (And.intro u3 (And.intro u1 (And.intro u10 u9)))))))))))) h

theorem clause13361 (t x01 x03 x12 x13 x14 x38 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x38)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x38)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x38)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x38)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6237 t x01 x03 x12 x13 x14 x38
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u5 (And.intro u4 u1)))))))) h

theorem clause13362 (t x01 x02 x06 x12 x13 x15 x26 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x06)) ≥ 0)) ∨ (¬ ((t + x26 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
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
  have u3 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x06)) ≥ 0) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6240 t x01 x02 x06 x12 x13 x15 x26 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u9 (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u7 (And.intro u8 (And.intro u6 (And.intro u3 (And.intro u2 u1))))))))))) h

theorem clause13363 (t x01 x02 x12 x13 x17 x24 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x17) + x67) ≥ 1))) := by
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
  have u3 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x17) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6242 t x01 x02 x12 x13 x17 x24 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u8 (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u2 (And.intro u6 (And.intro u5 u3)))))))))) h

theorem clause13365 (t x01 x02 x04 x12 x13 x17 x45 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x17) + x67) ≥ 1))) := by
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
  have u3 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x17) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6244 t x01 x02 x04 x12 x13 x17 x45 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u4 (And.intro u0 (And.intro u9 (And.intro u1 (And.intro u2 (And.intro u3 (And.intro u5 (And.intro u8 u6))))))))))) h

theorem clause13366 (t x01 x02 x12 x13 x16 x24 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x16) + x56) ≥ 1))) := by
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
  have u3 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x16) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6246 t x01 x02 x12 x13 x16 x24 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u8 (And.intro u0 (And.intro u6 (And.intro u4 (And.intro u7 (And.intro u1 (And.intro u2 u3)))))))))) h

theorem clause13367 (t x01 x02 x04 x12 x13 x17 x45 x58 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((t + x58 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1)))) := by
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
  have u3 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x58 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x45 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6248 t x01 x02 x04 x12 x13 x17 x45 x58 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u8 (And.intro u6 (And.intro u7 (And.intro u9 (And.intro u1 (And.intro u2 u3))))))))))) h

theorem clause13368 (t x01 x02 x12 x13 x17 x25 x27 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x27)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x17) + x57) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
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
  have u3 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x27)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x17) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6249 t x01 x02 x12 x13 x17 x25 x27 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u9 (And.intro u4 (And.intro u8 (And.intro u0 (And.intro u5 (And.intro u7 (And.intro u3 (And.intro u1 u2))))))))))) h

theorem clause13369 (t x01 x02 x04 x12 x13 x16 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x16) + x56) ≥ 1))) := by
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
  have u3 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x16) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6251 t x01 x02 x04 x12 x13 x16 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u9 (And.intro u5 (And.intro u3 (And.intro u6 (And.intro u7 u4))))))))))) h

theorem clause13370 (t x02 x03 x04 x12 x13 x25 x36 x45 x57 x68 x78 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1))) := by
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
  have u4 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((t + ((-1) * x68) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th6254 t x02 x03 x04 x12 x13 x25 x36 x45 x57 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u11 (And.intro u7 (And.intro u0 (And.intro u2 (And.intro u4 (And.intro u3 (And.intro u1 (And.intro u8 (And.intro u6 (And.intro u10 (And.intro u5 u9))))))))))))) h

theorem clause13371 (t x01 x02 x12 x13 x15 x26 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
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
  have u3 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x57) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6256 t x01 x02 x12 x13 x15 x26 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u8 (And.intro u1 (And.intro u5 (And.intro u7 u4)))))))))) h

theorem clause13372 (t x01 x02 x04 x12 x13 x17 x24 x45 x48 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x48)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x48)) ≤ (-1)))) := by
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
  have u3 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x04 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x24 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th6257 t x01 x02 x04 x12 x13 x17 x24 x45 x48 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u10 (And.intro u11 (And.intro u0 (And.intro u6 (And.intro u7 (And.intro u5 (And.intro u8 (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u9 u2))))))))))))) h

theorem clause13373 (t x01 x02 x12 x13 x17 x24 x48 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((t + x48 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x48)) ≥ 1))) := by
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
  have u3 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x48 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x24 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6258 t x01 x02 x12 x13 x17 x24 x48 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u2 (And.intro u6 (And.intro u7 (And.intro u0 (And.intro u1 (And.intro u4 u8)))))))))) h

theorem clause13374 (t x02 x04 x24 x45 x47 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x58)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ (x58 ≥ 0))) := by
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
  have u3 : ((x02 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x58 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6259 t x02 x04 x24 x45 x47 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u6 (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u5 u7))))))))) h

theorem clause13375 (t x24 x27 x34 x45 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x27)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
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
  have h := NineTheoryTrial.th6262 t x24 x27 x34 x45 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u3 (And.intro u5 (And.intro u7 (And.intro u0 (And.intro u4 u6))))))))) h

theorem clause13376 (t x01 x02 x12 x13 x17 x27 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x17) + x67) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
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
  have u3 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x17) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6263 t x01 x02 x12 x13 x17 x27 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u1 (And.intro u8 (And.intro u6 (And.intro u5 u2)))))))))) h

theorem clause13377 (t x02 x04 x12 x15 x24 x35 x45 x47 x57 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x15) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ (x45 ≥ 0)) ∨ ((t + ((-1) * x57)) ≤ 0) ∨ (¬ ((x15 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x47)) ≥ 1) := by
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
  have u6 : ((x35 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x12) + x15) ≥ 1) := by
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
  have u10 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x15 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th6264 t x02 x04 x12 x15 x24 x35 x45 x47 x57 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u10 (And.intro u8 (And.intro u6 (And.intro u0 (And.intro u9 (And.intro u3 (And.intro u1 (And.intro u5 (And.intro u4 (And.intro u7 (And.intro u11 u2))))))))))))) h

theorem clause13378 (t x02 x12 x15 x24 x35 x47 x56 x58 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x35 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x15) ≥ 1)) ∨ (¬ (x78 ≥ 0)) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x12) + x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x15 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th6266 t x02 x12 x15 x24 x35 x47 x56 x58 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u7 (And.intro u8 (And.intro u9 (And.intro u10 (And.intro u6 (And.intro u4 (And.intro u1 (And.intro u2 u5)))))))))))) h

theorem clause13379 (t x02 x03 x04 x24 x35 x46 x47 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + ((-1) * x02) + x03) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((t + x46 + ((-1) * x56)) ≥ 1))) := by
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
  have u3 : ((t + ((-1) * x02) + x03) ≥ 1) := by
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
  have u8 : ((t + x46 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6270 t x02 x03 x04 x24 x35 x46 x47 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u1 (And.intro u6 (And.intro u7 u8)))))))))) h

theorem clause13380 (t x01 x13 x14 x34 x37 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x34) + x37) ≥ 1))) := by
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
  have u3 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x34) + x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6273 t x01 x13 x14 x34 x37
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u5 (And.intro u0 (And.intro u3 u2))))))) h

theorem clause13381 (t x01 x03 x12 x13 x37 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x12) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6274 t x01 x03 x12 x13 x37
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u0 (And.intro u5 (And.intro u4 u2))))))) h

theorem clause13382 (t x02 x03 x24 x37 x46 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + ((-1) * x02) + x03) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((t + x68 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x02) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x68 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6275 t x02 x03 x24 x37 x46 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u7 (And.intro u2 (And.intro u0 (And.intro u6 (And.intro u1 (And.intro u3 u4))))))))) h

theorem clause13383 (t x02 x03 x07 x24 x37 x45 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x03) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((t + ((-1) * x37) + x57) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x02) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x37) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x03 + ((-1) * x07)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6276 t x02 x03 x07 x24 x37 x45 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u7 (And.intro u2 (And.intro u6 (And.intro u4 (And.intro u1 (And.intro u0 (And.intro u5 u8)))))))))) h

theorem clause13384 (x15 x45 x57 : ℝ) : ((¬ ((x15 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ ((x15 + ((-1) * x57)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x15 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x15 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6277 x15 x45 x57
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause13385 (t x02 x12 x24 x25 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6282 t x02 x12 x24 x25 x56
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u2 (And.intro u5 u0))))))) h

theorem clause13387 (t x01 x02 x03 x14 x24 x37 x45 x58 x78 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((t + x58 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x02)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x58 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x45 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6285 t x01 x02 x03 x14 x24 x37 x45 x58 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u8 (And.intro u0 (And.intro u1 (And.intro u9 (And.intro u7 (And.intro u6 (And.intro u3 u5))))))))))) h

theorem clause13388 (t x25 x26 x46 x56 x58 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((t + x56 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x25 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x56 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6292 t x25 x26 x46 x56 x58 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u4 (And.intro u5 u6)))))))) h

theorem clause13389 (t x01 x02 x15 x24 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x56 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6293 t x01 x02 x15 x24 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u4 (And.intro u3 (And.intro u1 (And.intro u7 (And.intro u0 (And.intro u5 u2))))))))) h

theorem clause13390 (t x14 x34 x35 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x14) + x34) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x14) + x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6294 t x14 x34 x35 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u4 u5))))))) h

theorem clause13391 (x15 x45 x56 : ℝ) : ((¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x45)) ≥ 0)) ∨ ((x15 + ((-1) * x56)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x15 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x15 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6295 x15 x45 x56
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause13392 (t x02 x12 x14 x24 x25 x45 x56 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x12) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x56 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x02) + x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x56 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6296 t x02 x12 x14 x24 x25 x45 x56 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u5 (And.intro u2 (And.intro u4 (And.intro u0 (And.intro u7 (And.intro u3 (And.intro u6 u1)))))))))) h

theorem clause13393 (t x14 x34 x36 x46 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x14) + x34) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x14) + x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6297 t x14 x34 x36 x46 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u4 u5))))))) h

theorem clause13394 (t x24 x26 x34 x46 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x24) + x34) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x26 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x24) + x34) ≥ 1) := by
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
  have h := NineTheoryTrial.th6298 t x24 x26 x34 x46 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u5 (And.intro u3 u2))))))) h

theorem clause13395 (t x03 x13 x14 x34 x35 x46 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x14)) ≥ 0)) ∨ ((t + ((-1) * x03)) ≤ 0) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ (x34 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x03)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6299 t x03 x13 x14 x34 x35 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u4 (And.intro u5 (And.intro u6 (And.intro u0 (And.intro u2 (And.intro u1 u3))))))))) h

theorem clause13396 (x14 x34 x46 : ℝ) : ((¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6300 x14 x34 x46
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u2 u0))) h

theorem clause13397 (t x02 x12 x24 x25 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x45)) ≥ 0)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x25 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6302 t x02 x12 x24 x25 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u7 (And.intro u5 u6))))))))) h

theorem clause13398 (t x02 x05 x12 x14 x24 x25 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x12) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x02) + x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x56 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6303 t x02 x05 x12 x14 x24 x25 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u7 (And.intro u4 (And.intro u8 (And.intro u3 (And.intro u2 (And.intro u9 (And.intro u6 (And.intro u1 u5))))))))))) h

theorem clause13399 (x03 x23 x35 x36 : ℝ) : ((¬ ((x35 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ ((x23 + ((-1) * x35)) ≤ (-1)) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0))) := by
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
  have u2 : ¬ ((x23 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th6305 x03 x23 x35 x36
  exact (fun hh => u2 (hh (And.intro u3 (And.intro u0 u1)))) h

theorem clause13400 (t x01 x03 x12 x13 : ℝ) : ((¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ ((t + x03 + ((-1) * x13)) ≥ 1) ∨ (¬ (x12 ≥ 0)) ∨ ((t + ((-1) * x01)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + x03 + ((-1) * x13)) ≥ 1) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr hh))))
  have h := NineTheoryTrial.th6306 t x01 x03 x12 x13
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u3 (And.intro u2 u0)))))) h

theorem clause13402 (t x02 x25 x27 x35 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + x25 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x57)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x25 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x25)) ≥ 1) := by
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
  have h := NineTheoryTrial.th6313 t x02 x25 x27 x35 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u1 (And.intro u3 (And.intro u4 u5))))))) h

theorem clause13403 (t x24 x35 x45 x47 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + ((-1) * x35) + x45) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x57)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x35) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6316 t x24 x35 x45 x47 x57
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u3 (And.intro u0 (And.intro u5 (And.intro u2 u4)))))) h

theorem clause13405 (t x03 x05 x34 x35 x36 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((t + ((-1) * x34) + x36) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x34) + x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6318 t x03 x05 x34 x35 x36 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u4 (And.intro u3 (And.intro u0 (And.intro u6 u1)))))))) h

theorem clause13407 (t x01 x02 x06 x12 x15 x36 x45 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x02) + x06) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x15 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x06 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x02) + x06) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th6322 t x01 x02 x06 x12 x15 x36 x45 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u10 (And.intro u0 (And.intro u5 (And.intro u7 (And.intro u8 (And.intro u4 (And.intro u9 (And.intro u11 (And.intro u6 (And.intro u3 (And.intro u1 u2))))))))))))) h

theorem clause13408 (t x01 x02 x03 x12 x24 x27 x36 x47 x67 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ (¬ ((t + x47 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x47)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x02)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x47 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x27 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6324 t x01 x02 x03 x12 x24 x27 x36 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u9 (And.intro u3 (And.intro u2 (And.intro u6 (And.intro u1 (And.intro u0 (And.intro u7 (And.intro u5 u8))))))))))) h

theorem clause13409 (t x04 x35 x45 x47 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + ((-1) * x35) + x45) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x57)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x35) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6325 t x04 x35 x45 x47 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u1 (And.intro u3 (And.intro u0 u4))))))) h

theorem clause13410 (t x01 x03 x12 x13 x16 x36 x67 x68 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((t + ((-1) * x67) + x68) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x68)) ≥ 1))) := by
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
  have u5 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x67) + x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x16 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6326 t x01 x03 x12 x13 x16 x36 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u8 (And.intro u3 (And.intro u4 (And.intro u1 (And.intro u0 (And.intro u5 (And.intro u6 u7)))))))))) h

theorem clause13411 (x05 x25 x56 : ℝ) : ((¬ ((x05 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ ((x25 + ((-1) * x56)) ≤ (-1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x05 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x25 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6328 x05 x25 x56
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause13412 (t x01 x03 x05 x12 x24 x35 x45 x57 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((t + ((-1) * x35) + x45) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x35) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6330 t x01 x03 x05 x12 x24 x35 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u6 (And.intro u8 (And.intro u5 (And.intro u4 (And.intro u3 (And.intro u2 (And.intro u0 u7)))))))))) h

theorem clause13413 (t x04 x12 x23 x24 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ ((t + ((-1) * x04)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x04)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6331 t x04 x12 x23 x24 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u4 (And.intro u3 u5)))))))) h

theorem clause13414 (t x01 x03 x12 x27 x37 x67 x78 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((t + x27 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x27 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6332 t x01 x03 x12 x27 x37 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u6 (And.intro u2 (And.intro u1 (And.intro u5 u7))))))))) h

theorem clause13415 (t x07 x35 x45 x47 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + ((-1) * x35) + x45) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x07 + ((-1) * x57)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x47)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x35) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x07 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x47)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6333 t x07 x35 x45 x47 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u3 u4)))))))) h

theorem clause13416 (t x04 x14 x46 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ ((t + ((-1) * x04)) ≤ 0) ∨ (¬ (x78 ≥ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x04)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6339 t x04 x14 x46 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u6 (And.intro u0 (And.intro u3 u2)))))))) h

theorem clause13417 (t x01 x02 x05 x12 x23 x24 x35 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x05) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x02)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((t + ((-1) * x01) + x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th6342 t x01 x02 x05 x12 x23 x24 x35 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u7 (And.intro u1 (And.intro u9 (And.intro u2 (And.intro u0 (And.intro u8 (And.intro u4 (And.intro u6 u10)))))))))))) h

theorem clause13418 (t x01 x03 x16 x35 x46 x56 x67 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x46 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x46 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6343 t x01 x03 x16 x35 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u3 (And.intro u2 (And.intro u7 (And.intro u6 u5))))))))) h

theorem clause13419 (x56 x67 x68 : ℝ) : ((¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x68)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x67 + ((-1) * x68)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6345 x56 x67 x68
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 u0))) h

theorem clause13420 (t x03 x23 x35 x36 x67 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6346 t x03 x23 x35 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u5 (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u1 u4)))))))) h

theorem clause13421 (t x04 x06 x45 x46 x47 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x45 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x06)) ≥ 0)) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((t + x45 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x45 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6347 t x04 x06 x45 x46 x47 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u6 (And.intro u0 (And.intro u2 (And.intro u3 u4)))))))) h

theorem clause13422 (t x01 x12 x17 x24 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ (x46 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ ((t + ((-1) * x17)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6348 t x01 x12 x17 x24 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u4 (And.intro u2 (And.intro u6 u5)))))))) h

theorem clause13423 (x14 x24 x46 : ℝ) : ((¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x24)) ≥ 0)) ∨ ((x14 + ((-1) * x46)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x14 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6350 x14 x24 x46
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause13425 (t x01 x03 x14 x36 x45 x57 x67 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6353 t x01 x03 x14 x36 x45 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u3 (And.intro u2 (And.intro u4 (And.intro u7 (And.intro u5 (And.intro u1 u0))))))))) h

theorem clause13426 (t x01 x03 x12 x24 x36 x46 x67 x78 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x46 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6354 t x01 x03 x12 x24 x36 x46 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u8 (And.intro u9 (And.intro u5 (And.intro u7 u4))))))))))) h

theorem clause13429 (t x04 x12 x23 x24 x34 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6365 t x04 x12 x23 x24 x34 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u5 (And.intro u7 u2))))))))) h

theorem clause13430 (t x04 x12 x14 x23 x34 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x14)) ≤ 0)) ∨ ((t + ((-1) * x45)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6366 t x04 x12 x14 x23 x34 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u0 (And.intro u5 (And.intro u6 (And.intro u8 (And.intro u7 (And.intro u2 u1)))))))))) h

theorem clause13431 (x04 x45 x47 : ℝ) : ((¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ ((x04 + ((-1) * x47)) ≥ 1) ∨ (¬ ((x45 + ((-1) * x47)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6370 x04 x45 x47
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause13432 (x05 x45 x57 : ℝ) : ((¬ ((x05 + ((-1) * x45)) ≥ 0)) ∨ ((x05 + ((-1) * x57)) ≥ 1) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x05 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6371 x05 x45 x57
  exact (fun hh => u1 (hh (And.intro u0 u2))) h

theorem clause13433 (t x01 x03 x12 x15 x23 x36 x57 x68 x78 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x15 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((t + ((-1) * x68) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th6373 t x01 x03 x12 x15 x23 x36 x57 x68 x78
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u9 (And.intro u7 (And.intro u6 (And.intro u5 (And.intro u1 (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u10 u8))))))))))) h

theorem clause13434 (t x01 x04 x16 x36 x45 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x04)) ≥ 1)) ∨ (¬ ((t + ((-1) * x36) + x56) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x01 + ((-1) * x04)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x36) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6377 t x01 x04 x16 x36 x45 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u4 (And.intro u3 (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u6 u7))))))))) h

theorem clause13435 (t x06 x12 x16 x23 x24 x26 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x23 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x26)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x16)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x23 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6378 t x06 x12 x16 x23 x24 x26 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u4 (And.intro u6 (And.intro u2 (And.intro u7 (And.intro u3 u5))))))))) h

theorem clause13436 (t x02 x13 x23 x27 x34 x37 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x37)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 + ((-1) * x37)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6379 t x02 x13 x23 x27 x34 x37
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u1 (And.intro u0 (And.intro u4 (And.intro u6 (And.intro u7 u5))))))))) h

theorem clause13437 (t x05 x12 x15 x23 x25 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((t + x23 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x15)) ≤ 0))) := by
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
  have u3 : ((t + x23 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6380 t x05 x12 x15 x23 x25 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u6 (And.intro u4 (And.intro u2 (And.intro u1 (And.intro u5 u0)))))))) h

theorem clause13438 (x04 x24 x45 x47 : ℝ) : ((¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x47)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th6382 x04 x24 x45 x47
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u2 (And.intro u1 u3)))) h

theorem clause13439 (t x01 x04 x06 x14 x36 x46 x47 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((t + ((-1) * x36) + x46) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x06) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x36) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x01) + x06) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6384 t x01 x04 x06 x14 x36 x46 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u6 (And.intro u7 (And.intro u3 u8)))))))))) h

theorem clause13440 (t x03 x04 x12 x14 x23 x36 x45 x47 x67 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((t + x47 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ ((t + ((-1) * x04)) ≤ 0) ∨ (¬ (x12 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x47 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x14 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ¬ ((t + ((-1) * x04)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th6385 t x03 x04 x12 x14 x23 x36 x45 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u5 (And.intro u10 (And.intro u0 (And.intro u9 (And.intro u7 (And.intro u2 (And.intro u1 (And.intro u8 (And.intro u4 u3)))))))))))) h

theorem clause13442 (t x03 x12 x23 x37 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6387 t x03 x12 x23 x37 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u4 (And.intro u6 (And.intro u5 u7))))))))) h

theorem clause13443 (t x03 x04 x07 x12 x14 x23 x37 x45 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ ((t + ((-1) * x04)) ≤ 0) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((t + ((-1) * x37) + x47) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x04)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x03 + ((-1) * x07)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((t + ((-1) * x37) + x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th6390 t x03 x04 x07 x12 x14 x23 x37 x45 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u0 (And.intro u5 (And.intro u4 (And.intro u2 (And.intro u10 (And.intro u8 (And.intro u11 (And.intro u3 (And.intro u1 (And.intro u7 u9))))))))))))) h

theorem clause13445 (t x01 x02 x12 x17 x23 x27 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x27) + x57) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x27) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x02 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6393 t x01 x02 x12 x17 x23 x27 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u5 (And.intro u6 (And.intro u9 (And.intro u8 (And.intro u7 u4))))))))))) h

theorem clause13446 (t x02 x12 x23 x24 x26 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ ((t + ((-1) * x24)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x26 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x26 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6394 t x02 x12 x23 x24 x26
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u6 (And.intro u5 u4)))))))) h

theorem clause13447 (t x03 x06 x12 x23 x36 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x68)) ≤ (-1))) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6396 t x03 x06 x12 x23 x36 x67 x68
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u4 (And.intro u5 (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u7 (And.intro u1 u8))))))))) h

theorem clause13449 (t x01 x16 x17 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x16 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x16 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6400 t x01 x16 x17 x67 x78
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u2 (And.intro u5 (And.intro u6 (And.intro u4 (And.intro u3 u0))))))) h

theorem clause13450 (x02 x04 x05 : ℝ) : ((¬ ((x02 + ((-1) * x05)) ≤ 0)) ∨ ((x02 + ((-1) * x04)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x05)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x04)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6401 x02 x04 x05
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u2 u1))) h

theorem clause13454 (t x02 x12 x13 x23 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((t + ((-1) * x02) + x12) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x02) + x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6413 t x02 x12 x13 x23 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u4 (And.intro u0 u3))))))) h

theorem clause13455 (t x13 x35 x37 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x35) + x45) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x57)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x35) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6414 t x13 x35 x37 x45 x57
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u5 (And.intro u2 (And.intro u4 (And.intro u1 u0)))))) h

theorem clause13456 (t x02 x03 x06 x12 x23 x24 x36 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x02) + x12) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((t + ((-1) * x36) + x46) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x02) + x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x36) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x03 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6419 t x02 x03 x06 x12 x23 x24 x36 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u6 (And.intro u8 (And.intro u0 (And.intro u2 (And.intro u7 (And.intro u4 (And.intro u1 u9))))))))))) h

theorem clause13457 (t x03 x12 x23 x36 x67 x78 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x12 ≥ 0)) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6422 t x03 x12 x23 x36 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u0 (And.intro u4 (And.intro u1 (And.intro u6 (And.intro u7 u2))))))))) h

theorem clause13458 (x12 x23 x25 : ℝ) : ((¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x25)) ≤ 0)) ∨ ((x12 + ((-1) * x25)) ≤ (-1))) := by
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
  have u2 : ¬ ((x12 + ((-1) * x25)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6423 x12 x23 x25
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause13460 (t x01 x02 x06 x12 x24 x26 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x06) ≥ 1)) ∨ (¬ ((t + x26 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x02)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x01) + x06) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x26 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6429 t x01 x02 x06 x12 x24 x26 x36 x67
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u2 (And.intro u3 (And.intro u7 (And.intro u8 (And.intro u1 (And.intro u5 (And.intro u6 u0))))))))) h

theorem clause13462 (t x02 x24 x27 : ℝ) : ((¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ (x27 ≥ 0)) ∨ ((t + ((-1) * x24) + x27) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x27 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x24) + x27) ≥ 1) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th6431 t x02 x24 x27
  exact (fun hh => u3 (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause13463 (t x03 x05 x12 x23 x35 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x03 + ((-1) * x05)) ≤ 0)) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6433 t x03 x05 x12 x23 x35 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u5 (And.intro u8 (And.intro u0 (And.intro u7 (And.intro u1 (And.intro u2 u6)))))))))) h

theorem clause13464 (t x01 x03 x04 x06 x12 x14 x23 x36 x45 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((t + ((-1) * x36) + x46) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x36) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))))
  have u12 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))))
  have h := NineTheoryTrial.th6436 t x01 x03 x04 x06 x12 x14 x23 x36 x45 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u12 (And.intro u10 (And.intro u0 (And.intro u7 (And.intro u1 (And.intro u2 (And.intro u9 (And.intro u3 (And.intro u6 (And.intro u5 (And.intro u8 u11)))))))))))))) h

theorem clause13465 (t x02 x23 x25 x35 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x58)) ≥ 1)) ∨ ((t + ((-1) * x35)) ≤ 0) ∨ (¬ ((x25 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6437 t x02 x23 x25 x35 x58
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u3 (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u0 u4))))))) h

theorem clause13466 (t x23 x35 x36 : ℝ) : ((¬ (x23 ≥ 0)) ∨ ((t + ((-1) * x35) + x36) ≥ 1) ∨ ((t + ((-1) * x35)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x35) + x36) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th6439 t x23 x35 x36
  exact (fun hh => u1 (hh (And.intro u3 (And.intro u0 u2)))) h

theorem clause13467 (t x23 x25 x36 x45 x56 x58 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x23 + ((-1) * x25)) ≥ 1)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x58)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x23 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6440 t x23 x25 x36 x45 x56 x58 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u0 (And.intro u8 (And.intro u4 (And.intro u9 (And.intro u1 (And.intro u3 (And.intro u5 (And.intro u6 u2))))))))))) h

theorem clause13468 (t x02 x12 x23 x26 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ ((t + ((-1) * x68)) ≤ 0) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x68)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6442 t x02 x12 x23 x26 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u3 (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u4 u1)))))))) h

theorem clause13469 (t x02 x23 x27 x37 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x27 + ((-1) * x37)) ≤ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 + ((-1) * x37)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6445 t x02 x23 x27 x37 x67 x78
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u1 (And.intro u0 (And.intro u7 (And.intro u5 (And.intro u4 (And.intro u2 u3)))))))) h

theorem clause13470 (t x12 x25 x27 x35 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + x25 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x57)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x27)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x25 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6446 t x12 x25 x27 x35 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u5 u3))))))) h

theorem clause13472 (t x01 x03 x05 x14 x36 x48 x56 x67 x78 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + x48 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x48)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x56)) ≥ 0) := by
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
  have u7 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x48 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x14 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6451 t x01 x03 x05 x14 x36 x48 x56 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u7 (And.intro u0 (And.intro u8 (And.intro u9 (And.intro u6 (And.intro u5 u4))))))))))) h

theorem clause13473 (t x02 x12 x23 x27 x37 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x27 + ((-1) * x37)) ≤ 0)) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 + ((-1) * x37)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6452 t x02 x12 x23 x27 x37 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u6 (And.intro u0 (And.intro u5 (And.intro u7 (And.intro u3 u1))))))))) h

theorem clause13475 (x35 x56 x57 : ℝ) : ((¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x57)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6456 x35 x56 x57
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u2 u0))) h

theorem clause13477 (t x06 x16 x56 : ℝ) : ((¬ ((x06 + ((-1) * x16)) ≥ 0)) ∨ ((t + x06 + ((-1) * x56)) ≥ 1) ∨ (¬ ((t + x16 + ((-1) * x56)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x06 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + x06 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + x16 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6460 t x06 x16 x56
  exact (fun hh => u1 (hh (And.intro u0 u2))) h

theorem clause13480 (x01 x02 x04 : ℝ) : (((x01 + ((-1) * x02)) ≥ 0) ∨ (¬ ((x02 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x04)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x02)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6465 x01 x02 x04
  exact (fun hh => u0 (hh (And.intro u2 u1))) h

theorem clause13481 (x45 x57 x58 : ℝ) : (((x45 + ((-1) * x58)) ≤ (-1)) ∨ (¬ ((x57 + ((-1) * x58)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x58)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ((x57 + ((-1) * x58)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6466 x45 x57 x58
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause13482 (t x13 x34 x36 : ℝ) : ((¬ (x13 ≥ 0)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ ((t + ((-1) * x34) + x36) ≥ 1) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x34) + x36) ≥ 1) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th6468 t x13 x34 x36
  exact (fun hh => u2 (hh (And.intro u0 (And.intro u3 u1)))) h

theorem clause13483 (x05 x35 x57 : ℝ) : ((¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x35)) ≥ 0)) ∨ ((x05 + ((-1) * x57)) ≥ 1)) := by
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
  have u2 : ¬ ((x05 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6469 x05 x35 x57
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause13484 (t x02 x04 x12 x24 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x12) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x02) + x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6470 t x02 x04 x12 x24 x46
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u2 (And.intro u5 (And.intro u1 (And.intro u4 u0)))))) h

theorem clause13485 (t x12 x14 x24 x26 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + ((-1) * x24) + x26) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x24) + x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6471 t x12 x14 x24 x26 x45
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u1 (And.intro u5 (And.intro u0 (And.intro u3 u2)))))) h

theorem clause13486 (x12 x25 x26 : ℝ) : ((¬ ((x25 + ((-1) * x26)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x25 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6473 x12 x25 x26
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u2 u1))) h

theorem clause13487 (x03 x35 x37 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x37)) ≥ 0)) ∨ ((x03 + ((-1) * x37)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x03 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6482 x03 x35 x37
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause13488 (x03 x35 x36 : ℝ) : ((¬ ((x35 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ ((x03 + ((-1) * x36)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x03 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6483 x03 x35 x36
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause13489 (t x03 x12 x23 x24 x25 x35 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((t + ((-1) * x03) + x23) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x25 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x03) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6484 t x03 x12 x23 x24 x25 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u5 (And.intro u6 (And.intro u2 (And.intro u1 u0)))))))) h

theorem clause13491 (t x02 x24 x26 x46 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ ((t + ((-1) * x24)) ≤ 0) ∨ (¬ (x46 ≥ 0)) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6489 t x02 x24 x26 x46 x68
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u0 (And.intro u2 (And.intro u1 (And.intro u3 (And.intro u5 u4))))))) h

theorem clause13493 (t x14 x35 x45 x47 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + ((-1) * x35) + x45) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x57)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x35) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6492 t x14 x35 x45 x47 x57
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u1 (And.intro u0 (And.intro u4 (And.intro u5 u2)))))) h

theorem clause13494 (t x14 x24 x34 : ℝ) : ((¬ ((t + x14 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x34)) ≤ 0)) ∨ ((t + x14 + ((-1) * x24)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + x14 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + x14 + ((-1) * x24)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6493 t x14 x24 x34
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause13495 (x04 x24 x34 : ℝ) : ((¬ ((x24 + ((-1) * x34)) ≤ 0)) ∨ ((x04 + ((-1) * x34)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x24)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x24 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6495 x04 x24 x34
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause13496 (t x02 x06 x23 x24 x25 x26 x36 x56 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((t + x23 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((t + ((-1) * x36) + x56) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x26)) ≤ 0)) ∨ ((x06 + ((-1) * x26)) ≤ 0) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x23 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x36) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((x06 + ((-1) * x26)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6496 t x02 x06 x23 x24 x25 x26 x36 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u9 (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u7 (And.intro u4 (And.intro u6 (And.intro u0 u5))))))))))) h

theorem clause13497 (t x02 x04 x24 x25 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((t + ((-1) * x24) + x25) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x24) + x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6498 t x02 x04 x24 x25 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u0 u3))))))) h

theorem clause13498 (t x02 x23 x25 x35 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ ((t + ((-1) * x35)) ≤ 0) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6503 t x02 x23 x25 x35 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u2 (And.intro u4 (And.intro u0 (And.intro u1 (And.intro u3 u5)))))))) h

theorem clause13499 (t x01 x05 x13 x36 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x05)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x67) + x68) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x01 + ((-1) * x05)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x67) + x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6504 t x01 x05 x13 x36 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u6 (And.intro u7 (And.intro u3 u1))))))))) h

theorem clause13500 (t x01 x02 x13 x24 x26 x36 x46 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ ((t + ((-1) * x24)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x67) + x68) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((t + ((-1) * x67) + x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th6506 t x01 x02 x13 x24 x26 x36 x46 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u10 (And.intro u8 (And.intro u5 (And.intro u9 (And.intro u4 (And.intro u6 (And.intro u7 u3)))))))))))) h

theorem clause13501 (x16 x36 x67 : ℝ) : ((¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x36)) ≤ 0)) ∨ ((x16 + ((-1) * x67)) ≤ (-1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x16 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x16 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6507 x16 x36 x67
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause13502 (t x04 x05 x12 x15 x23 x24 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((t + x23 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x15)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1)))) := by
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
  have u3 : ((x04 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6508 t x04 x05 x12 x15 x23 x24 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u6 (And.intro u7 u1))))))))) h

theorem clause13503 (t x02 x12 x23 x24 x26 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((t + x23 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x23 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6511 t x02 x12 x23 x24 x26
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u3 (And.intro u4 (And.intro u1 (And.intro u0 u2)))))) h

theorem clause13504 (t x01 x06 x12 x25 x36 x45 x56 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + ((-1) * x36) + x56) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x06) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x25 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x36) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x01) + x06) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6513 t x01 x06 x12 x25 x36 x45 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u6 (And.intro u0 (And.intro u2 (And.intro u3 (And.intro u7 (And.intro u4 (And.intro u5 u8)))))))))) h

theorem clause13505 (x25 x45 x56 : ℝ) : ((¬ ((x25 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ ((x25 + ((-1) * x56)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x25 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x25 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6514 x25 x45 x56
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause13506 (x02 x26 : ℝ) : ((¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th6521 x02 x26
  exact (fun hh => (Or.elim hh (fun hh => hh u1) (fun zz => ((fun hh => hh u0) zz)))) h

theorem clause13507 (x01 x02 : ℝ) : (((x01 + ((-1) * x02)) ≤ 0) ∨ ((x01 + ((-1) * x02)) ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x02)) ≥ 0) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th6522 x01 x02
  exact (fun hh => (Or.elim hh u1 (fun zz => (u0 zz)))) h

theorem clause13508 (x04 x24 x45 : ℝ) : ((¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x24)) ≤ 0)) ∨ ((x24 + ((-1) * x45)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x24 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6523 x04 x24 x45
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause13509 (x06 x26 x56 : ℝ) : (((x06 + ((-1) * x56)) ≤ 0) ∨ (¬ ((x06 + ((-1) * x26)) ≤ 0)) ∨ (¬ ((x26 + ((-1) * x56)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ((x06 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x26 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6527 x06 x26 x56
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 u0))) h

theorem clause13511 (t x02 x03 x06 x12 x23 x24 x25 x26 x36 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((t + x23 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x26)) ≤ 0)) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x23 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x03 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x06 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))))
  have u12 : ((x26 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))))
  have u13 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))))
  have h := NineTheoryTrial.th6549 t x02 x03 x06 x12 x23 x24 x25 x26 x36 x56 x67 x68
  exact (fun hh => (fun hh => hh u13) (hh (And.intro u6 (And.intro u7 (And.intro u5 (And.intro u3 (And.intro u1 (And.intro u8 (And.intro u10 (And.intro u12 (And.intro u9 (And.intro u11 (And.intro u4 (And.intro u2 u0)))))))))))))) h

theorem clause13513 (t x01 x03 x12 x14 x23 x36 x47 x68 x78 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ (x12 ≥ 0)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x68) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th6555 t x01 x03 x12 x14 x23 x36 x47 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u10 (And.intro u8 (And.intro u6 (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u7 (And.intro u4 u9)))))))))))) h

theorem clause13514 (x12 x23 x26 : ℝ) : ((¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x26)) ≤ 0)) ∨ ((x12 + ((-1) * x26)) ≤ (-1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x12 + ((-1) * x26)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6557 x12 x23 x26
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause13516 (t x14 x36 x45 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ ((t + ((-1) * x36)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x45 ≥ 0))) := by
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
  have u3 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6562 t x14 x36 x45 x46 x67
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u4 (And.intro u5 (And.intro u3 (And.intro u0 (And.intro u6 u2))))))) h

theorem clause13517 (t x05 x12 x25 x27 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x05) + x25) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x57)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x27)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x05) + x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6566 t x05 x12 x25 x27 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u4 (And.intro u5 u0))))))) h

theorem clause13518 (t x02 x03 x12 x23 x24 x36 x47 x67 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x02) + x12) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((t + x47 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x02) + x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x47 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6568 t x02 x03 x12 x23 x24 x36 x47 x67
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 (And.intro u6 (And.intro u7 (And.intro u8 (And.intro u0 (And.intro u4 (And.intro u5 u3))))))))) h

theorem clause13519 (x15 x25 x57 : ℝ) : ((¬ ((x15 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x15 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6569 x15 x25 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 u1)))) h

theorem clause13520 (t x12 x23 x27 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6573 t x12 x23 x27 x67 x78
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u2 u4))))))) h

theorem clause13521 (t x04 x12 x23 x24 x34 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6576 t x04 x12 x23 x24 x34 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u6 (And.intro u5 (And.intro u3 (And.intro u4 (And.intro u0 u7))))))))) h

theorem clause13522 (t x01 x02 x03 x12 x23 x26 x35 x56 x68 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ ((t + ((-1) * x68)) ≤ 0) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x02)) ≥ 0) := by
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
  have u7 : ¬ ((t + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th6578 t x01 x02 x03 x12 x23 x26 x35 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u7 (And.intro u8 (And.intro u9 (And.intro u10 (And.intro u2 (And.intro u5 (And.intro u0 (And.intro u3 (And.intro u1 u6)))))))))))) h

theorem clause13523 (t x06 x12 x23 x26 x56 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x06 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6579 t x06 x12 x23 x26 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u3 (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u6 (And.intro u4 u2))))))))) h

theorem clause13524 (x03 x36 x37 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x37)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x36 + ((-1) * x37)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6581 x03 x36 x37
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 u0)))) h

theorem clause13526 (x24 x34 x46 : ℝ) : ((¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x34)) ≤ 0)) ∨ ((x34 + ((-1) * x46)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x34 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6584 x24 x34 x46
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause13527 (t x02 x12 x23 x24 x27 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1))) ∨ ((t + ((-1) * x27)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≥ 0) := by
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
  have u5 : ((x02 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6587 t x02 x12 x23 x24 x27
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u6 (And.intro u1 (And.intro u4 u5)))))))) h

theorem clause13528 (t x02 x12 x23 x27 x35 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ (x35 ≥ 0)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6588 t x02 x12 x23 x27 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u6 (And.intro u2 u3)))))))) h

theorem clause13530 (t x06 x12 x23 x26 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x26)) ≥ 0)) ∨ ((t + ((-1) * x36)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6591 t x06 x12 x23 x26 x36 x67
  exact (fun hh => (fun hh => hh u7) (hh (And.intro u6 (And.intro u5 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u4 u2)))))))) h

theorem clause13531 (x36 x56 x67 : ℝ) : ((¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x36 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6592 x36 x56 x67
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u2 u1))) h

theorem clause13532 (t x03 x06 x34 x35 x36 x67 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x34) + x35) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x34) + x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6594 t x03 x06 x34 x35 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u6 (And.intro u2 (And.intro u0 u3)))))))) h

theorem clause13533 (t x01 x02 x03 x12 x24 x27 x35 x57 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + x27 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x02)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
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
  have u8 : ((x12 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6595 t x01 x02 x03 x12 x24 x27 x35 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u3 (And.intro u6 (And.intro u0 (And.intro u8 (And.intro u2 (And.intro u4 u7)))))))))) h

theorem clause13534 (x24 x46 x47 : ℝ) : (((x24 + ((-1) * x47)) ≤ (-1)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x47)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x47)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6596 x24 x46 x47
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause13535 (x04 x34 : ℝ) : (((x04 + ((-1) * x34)) ≤ 0) ∨ ((x04 + ((-1) * x34)) ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x34)) ≥ 0) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th6598 x04 x34
  exact (fun hh => (Or.elim hh u1 (fun zz => (u0 zz)))) h

theorem clause13536 (x26 x46 x67 : ℝ) : ((¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x26 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6599 x26 x46 x67
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 u0))) h

theorem clause13537 (x02 x12 x27 : ℝ) : ((¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6600 x02 x12 x27
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause13538 (t x05 x24 x25 x34 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x24 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x24 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6603 t x05 x24 x25 x34 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u6 (And.intro u2 u5)))))))) h

theorem clause13539 (t x04 x35 x45 x46 x56 : ℝ) : ((¬ ((x46 + ((-1) * x56)) ≤ 0)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x35) + x45) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x46 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x35) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6604 t x04 x35 x45 x46 x56
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u4 (And.intro u2 (And.intro u5 (And.intro u0 u1)))))) h

theorem clause13540 (t x01 x03 x04 x12 x27 x34 x46 x47 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((t + x27 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x27 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6605 t x01 x03 x04 x12 x27 x34 x46 x47
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u8 (And.intro u2 (And.intro u7 (And.intro u1 (And.intro u0 (And.intro u5 (And.intro u6 u4))))))))) h

theorem clause13541 (x36 x46 x68 : ℝ) : ((¬ ((x36 + ((-1) * x46)) ≤ 0)) ∨ ((x46 + ((-1) * x68)) ≥ 1) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x36 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x46 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6607 x36 x46 x68
  exact (fun hh => u1 (hh (And.intro u0 u2))) h

theorem clause13542 (x46 x56 x67 : ℝ) : (((x56 + ((-1) * x67)) ≤ (-1)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x56)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6608 x46 x56 x67
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause13543 (t x12 x23 x27 x34 x37 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + x34 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x27 + ((-1) * x37)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x34 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 + ((-1) * x37)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6609 t x12 x23 x27 x34 x37
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u3 (And.intro u2 u0))))))) h

theorem clause13544 (t x03 x23 x34 x36 x46 x67 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x46)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6610 t x03 x23 x34 x36 x46 x67
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u6 (And.intro u5 (And.intro u1 u7)))))))) h

theorem clause13546 (t x03 x34 x36 x67 x78 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x34 ≥ 0)) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6612 t x03 x34 x36 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u1 (And.intro u6 (And.intro u3 (And.intro u4 u0)))))))) h

theorem clause13547 (t x23 x27 x34 x37 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((t + x34 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x27)) ≤ 0)) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x34 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x27)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6614 t x23 x27 x34 x37 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u0 (And.intro u4 (And.intro u1 u2))))))) h

theorem clause13548 (t x01 x03 x12 x27 x34 x46 x67 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x27 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x27 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6618 t x01 x03 x12 x27 x34 x46 x67
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u7 (And.intro u2 (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u5 u6)))))))) h

theorem clause13549 (t x24 x34 x45 x46 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ (x24 ≥ 0)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6623 t x24 x34 x45 x46 x57 x67
  exact (fun hh => (fun hh => hh u7) (hh (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 (And.intro u6 (And.intro u1 u0)))))))) h

theorem clause13550 (t x25 x34 x45 x46 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + x25 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x25 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6625 t x25 x34 x45 x46 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u3 u4))))))) h

theorem clause13551 (t x24 x34 x36 x46 x47 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x24 ≥ 0)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1)) ∨ ((t + ((-1) * x47)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x24 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6627 t x24 x34 x36 x46 x47 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u2 (And.intro u6 (And.intro u5 (And.intro u3 (And.intro u1 (And.intro u4 u0))))))))) h

theorem clause13553 (t x24 x34 x46 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x24 ≥ 0)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x24 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6630 t x24 x34 x46 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u0 (And.intro u4 (And.intro u5 (And.intro u3 (And.intro u2 u1)))))))) h

theorem clause13554 (t x01 x02 x03 x27 x34 x47 x57 x78 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x47) + x57) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x47) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x02)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6632 t x01 x02 x03 x27 x34 x47 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u8 (And.intro u3 (And.intro u2 (And.intro u7 (And.intro u1 u6)))))))))) h

theorem clause13555 (t x01 x02 x03 x25 x36 x57 x68 x78 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x02)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x68) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6633 t x01 x02 x03 x25 x36 x57 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u2 (And.intro u8 (And.intro u1 (And.intro u0 (And.intro u5 (And.intro u6 (And.intro u3 u4)))))))))) h

theorem clause13556 (t x01 x02 x04 x12 x24 x25 x34 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((t + x24 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x04) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x02)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x24 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x01) + x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6635 t x01 x02 x04 x12 x24 x25 x34 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u8 (And.intro u7 (And.intro u6 (And.intro u4 (And.intro u2 (And.intro u3 u5)))))))))) h

theorem clause13557 (t x12 x23 x25 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6636 t x12 x23 x25 x45 x57
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u4 (And.intro u1 (And.intro u5 (And.intro u0 (And.intro u2 u3))))))) h

theorem clause13558 (t x02 x04 x23 x24 x25 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((t + x23 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x23 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6638 t x02 x04 x23 x24 x25 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u4 (And.intro u1 u6)))))))) h

theorem clause13559 (t x01 x03 x04 x15 x34 x46 x47 x57 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x47) + x57) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x47) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6640 t x01 x03 x04 x15 x34 x46 x47 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u8 (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 (And.intro u7 (And.intro u0 u6)))))))))) h

theorem clause13560 (t x05 x34 x45 x46 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + x05 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x05 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6644 t x05 x34 x45 x46 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u2 (And.intro u3 (And.intro u1 u4))))))) h

theorem clause13561 (t x01 x02 x03 x12 x23 x27 x34 x46 x67 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x02)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x12 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x02 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th6645 t x01 x02 x03 x12 x23 x27 x34 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u2 (And.intro u4 (And.intro u1 (And.intro u8 (And.intro u7 (And.intro u3 (And.intro u6 (And.intro u9 u10)))))))))))) h

theorem clause13562 (t x02 x07 x12 x23 x27 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + x23 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x23 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x07)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6646 t x02 x07 x12 x23 x27 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u2 (And.intro u6 (And.intro u1 (And.intro u0 u4)))))))) h

theorem clause13563 (t x01 x03 x07 x12 x17 x23 x34 x46 x68 x78 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x17)) ≤ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ ((t + ((-1) * x68)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x07)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x17)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x07 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ¬ ((t + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x01 + ((-1) * x07)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th6647 t x01 x03 x07 x12 x17 x23 x34 x46 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u9 (And.intro u10 (And.intro u2 (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u5 (And.intro u7 (And.intro u11 (And.intro u8 u6))))))))))))) h

theorem clause13564 (t x01 x03 x17 x34 x46 x68 x78 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x68) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6648 t x01 x03 x17 x34 x46 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u4 (And.intro u3 (And.intro u5 (And.intro u6 u7))))))))) h

theorem clause13565 (t x01 x12 x17 x23 x27 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((t + x23 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x27)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x23 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 + ((-1) * x27)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6649 t x01 x12 x17 x23 x27
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u5 (And.intro u1 (And.intro u4 (And.intro u2 u0)))))) h

theorem clause13566 (t x02 x12 x24 x25 x27 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x24 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1))) ∨ ((t + ((-1) * x27)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x24 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6650 t x02 x12 x24 x25 x27
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u2 (And.intro u4 (And.intro u0 (And.intro u5 (And.intro u3 u1)))))))) h

theorem clause13570 (t x01 x03 x15 x34 x46 x57 x67 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6656 t x01 x03 x15 x34 x46 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u2 (And.intro u5 (And.intro u3 (And.intro u6 (And.intro u0 u7))))))))) h

theorem clause13571 (t x01 x03 x05 x12 x15 x23 x34 x46 x57 x67 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x15)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x12 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th6657 t x01 x03 x05 x12 x15 x23 x34 x46 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u4 (And.intro u9 (And.intro u2 (And.intro u8 (And.intro u1 (And.intro u7 (And.intro u5 (And.intro u11 (And.intro u0 (And.intro u3 u10))))))))))))) h

theorem clause13572 (t x02 x07 x23 x25 x27 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x23 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x27)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x07)) ≥ 0)) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x23 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x07 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x27)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x07)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6658 t x02 x07 x23 x25 x27 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u5 (And.intro u0 (And.intro u3 (And.intro u6 u1)))))))) h

theorem clause13573 (t x01 x03 x04 x12 x27 x34 x45 x47 x78 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1)) ∨ (¬ (x78 ≥ 0)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th6659 t x01 x03 x04 x12 x27 x34 x45 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u8 (And.intro u3 (And.intro u7 (And.intro u1 (And.intro u5 (And.intro u4 (And.intro u9 (And.intro u2 (And.intro u0 u10)))))))))))) h

theorem clause13574 (t x01 x02 x03 x12 x25 x27 x36 x67 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x27 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x02)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x27 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6661 t x01 x02 x03 x12 x25 x27 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u8 (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u7 (And.intro u5 u6)))))))))) h

theorem clause13576 (t x01 x03 x15 x36 x58 x67 x78 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x58 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x58)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x58 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x15 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6663 t x01 x03 x15 x36 x58 x67 x78
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u5 (And.intro u2 (And.intro u3 (And.intro u7 (And.intro u0 (And.intro u4 u1)))))))) h

theorem clause13577 (t x12 x15 x23 x25 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((t + x23 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x15)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x58)) ≤ (-1)))) := by
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
  have u3 : ((x25 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6664 t x12 x15 x23 x25 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u4 u3))))))) h

theorem clause13578 (t x34 x37 x45 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((t + ((-1) * x45) + x47) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x37)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x45) + x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6666 t x34 x37 x45 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u5 u4))))))) h

theorem clause13579 (x26 x46 x67 : ℝ) : ((¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x46)) ≤ 0)) ∨ ((x26 + ((-1) * x67)) ≤ (-1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x26 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x26 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6669 x26 x46 x67
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause13580 (t x04 x07 x24 x37 x46 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x24 ≥ 0)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ ((t + ((-1) * x37)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x24 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x07)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x37)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6670 t x04 x07 x24 x37 x46 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u5 (And.intro u7 (And.intro u0 (And.intro u6 (And.intro u2 u3))))))))) h

theorem clause13581 (t x25 x34 x45 x47 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((t + x25 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x57)) ≥ 0)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x25 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6677 t x25 x34 x45 x47 x57
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u3 u4)))))) h

theorem clause13582 (t x02 x03 x23 x24 x25 x34 x45 x47 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + x23 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((t + ((-1) * x45) + x47) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
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
  have u3 : ((t + x23 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x45) + x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6679 t x02 x03 x23 x24 x25 x34 x45 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u7 (And.intro u4 (And.intro u3 (And.intro u8 u6)))))))))) h

theorem clause13583 (t x02 x04 x23 x24 x25 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((t + x23 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x24)) ≤ 0) := by
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
  have u5 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6680 t x02 x04 x23 x24 x25 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u4 (And.intro u2 (And.intro u3 (And.intro u5 (And.intro u1 u0)))))))) h

theorem clause13585 (t x01 x02 x03 x12 x26 x27 x35 x56 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + x26 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x02)) ≥ 0) := by
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
  have u5 : ((t + x26 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6687 t x01 x02 x03 x12 x26 x27 x35 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u8 (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u3 (And.intro u0 (And.intro u7 u6)))))))))) h

theorem clause13586 (t x02 x04 x23 x24 x27 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + x23 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x23 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6688 t x02 x04 x23 x24 x27 x46
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u1 (And.intro u4 (And.intro u3 (And.intro u0 (And.intro u5 u2))))))) h

theorem clause13587 (t x04 x34 x45 x46 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ ((t + ((-1) * x47)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6689 t x04 x34 x45 x46 x47
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u0 (And.intro u4 (And.intro u6 (And.intro u5 (And.intro u1 u3))))))) h

theorem clause13588 (t x04 x23 x24 x45 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6692 t x04 x23 x24 x45 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u1 (And.intro u0 (And.intro u7 (And.intro u4 (And.intro u2 (And.intro u3 u5))))))))) h

theorem clause13589 (t x01 x02 x12 x23 x27 x34 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ (x34 ≥ 0)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x02)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6695 t x01 x02 x12 x23 x27 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u0 (And.intro u6 (And.intro u5 (And.intro u1 (And.intro u2 (And.intro u4 u3))))))))) h

theorem clause13590 (t x04 x34 x45 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ (x04 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x04 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6696 t x04 x34 x45 x46 x67
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u5 (And.intro u6 (And.intro u0 (And.intro u1 (And.intro u4 u3))))))) h

theorem clause13591 (x35 x45 x56 : ℝ) : ((¬ ((x35 + ((-1) * x45)) ≤ 0)) ∨ ((x45 + ((-1) * x56)) ≥ 1) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6697 x35 x45 x56
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause13592 (x05 x25 x45 : ℝ) : ((¬ ((x05 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((x25 + ((-1) * x45)) ≤ 0)) ∨ ((x05 + ((-1) * x45)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x05 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x25 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x05 + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6704 x05 x25 x45
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause13593 (x25 x45 x57 : ℝ) : ((¬ ((x25 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ ((x25 + ((-1) * x57)) ≤ (-1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x25 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x25 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6705 x25 x45 x57
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause13594 (t x02 x05 x24 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x24 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ ((t + ((-1) * x57)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x24 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x24)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6706 t x02 x05 x24 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u3 (And.intro u4 (And.intro u1 (And.intro u2 (And.intro u7 (And.intro u0 u5))))))))) h

theorem clause13596 (t x01 x07 x14 x37 x45 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + x37 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + x01 + ((-1) * x07)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x07 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x37 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x01 + ((-1) * x07)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th6713 t x01 x07 x14 x37 x45 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u6 (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u5 u4))))))))) h

theorem clause13597 (t x05 x07 x56 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x56 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x07)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6714 t x05 x07 x56 x57 x78
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u4 (And.intro u2 (And.intro u3 (And.intro u0 u1)))))) h

theorem clause13598 (x02 x24 x27 : ℝ) : ((¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x27)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x27)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6717 x02 x24 x27
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 u0))) h

theorem clause13599 (t x01 x02 x12 x14 x25 x26 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x14) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x02)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x12) + x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6725 t x01 x02 x12 x14 x25 x26
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u3 (And.intro u4 (And.intro u5 (And.intro u0 (And.intro u2 u1))))))) h

theorem clause13601 (t x02 x23 x24 x34 x37 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((t + x34 + ((-1) * x37)) ≥ 1))) := by
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
  have u4 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x34 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6733 t x02 x23 x24 x34 x37
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u4 (And.intro u1 u5))))))) h

theorem clause13602 (x05 x25 x45 : ℝ) : ((¬ ((x05 + ((-1) * x25)) ≤ 0)) ∨ ((x25 + ((-1) * x45)) ≥ 0) ∨ (¬ ((x05 + ((-1) * x45)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x05 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x45)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6735 x05 x25 x45
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 u0))) h

theorem clause13605 (x03 x35 x37 : ℝ) : (((x03 + ((-1) * x35)) ≥ 1) ∨ (¬ ((x35 + ((-1) * x37)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x37)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6755 x03 x35 x37
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause13607 (x04 x24 x45 : ℝ) : ((¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x24)) ≤ 0)) ∨ ((x04 + ((-1) * x45)) ≤ (-1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x04 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6787 x04 x24 x45
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause13608 (t x02 x07 x23 x27 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + x23 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x23 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x07)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6790 t x02 x07 x23 x27 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u3 u1))))))) h

theorem clause13609 (t x02 x04 x23 x26 x36 x45 x46 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + x67 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x26 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x67 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x26 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th6795 t x02 x04 x23 x26 x36 x45 x46 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u6 (And.intro u5 (And.intro u0 (And.intro u10 (And.intro u7 (And.intro u11 (And.intro u1 (And.intro u2 (And.intro u3 (And.intro u4 u9))))))))))))) h

theorem clause13610 (t x02 x23 x25 x26 x36 x57 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x23 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x23 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x68) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6803 t x02 x23 x25 x26 x36 x57 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u6 (And.intro u1 (And.intro u7 (And.intro u5 (And.intro u2 (And.intro u8 u4)))))))))) h

theorem clause13611 (x05 x25 x56 x57 : ℝ) : ((¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((x56 + ((-1) * x57)) ≥ 0)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th6816 x05 x25 x56 x57
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u1 (And.intro u2 u0)))) h

theorem clause13612 (t x06 x35 x36 x45 x56 x68 : ℝ) : ((¬ ((x35 + ((-1) * x36)) ≥ 0)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x35) + x45) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x35) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6821 t x06 x35 x36 x45 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u6 (And.intro u1 (And.intro u5 (And.intro u0 (And.intro u4 u2)))))))) h

theorem clause13614 (t x02 x04 x23 x24 x26 x46 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x23 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x67) + x68) ≥ 1))) := by
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
  have u3 : ((x04 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x68)) ≥ 1) := by
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
  have u8 : ((t + ((-1) * x67) + x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6841 t x02 x04 x23 x24 x26 x46 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u3 (And.intro u4 (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u6 u8)))))))))) h

theorem clause13616 (t x12 x25 x27 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x25) + x45) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x27 + ((-1) * x57)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x25) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6847 t x12 x25 x27 x45 x57
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u5 (And.intro u0 (And.intro u4 (And.intro u1 u3)))))) h

theorem clause13617 (t x04 x05 x12 x24 x56 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x05)) ≥ 0) := by
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
  have u7 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6848 t x04 x05 x12 x24 x56 x67 x78
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u5 (And.intro u0 (And.intro u7 (And.intro u4 u8))))))))) h

theorem clause13618 (x04 x05 x24 x34 x46 x56 : ℝ) : ((¬ ((x46 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x05)) ≥ 0)) ∨ ((x34 + ((-1) * x46)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x46 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x34)) ≤ 0) := by
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
  have u5 : ¬ ((x34 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th6862 x04 x05 x24 x34 x46 x56
  exact (fun hh => u5 (hh (And.intro u4 (And.intro u3 (And.intro u0 (And.intro u2 u1)))))) h

theorem clause13619 (t x02 x26 x27 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ (x67 ≥ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1)) ∨ ((t + ((-1) * x26)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x26)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6870 t x02 x26 x27 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u2 (And.intro u3 (And.intro u5 (And.intro u4 (And.intro u1 u0)))))))) h

theorem clause13620 (t x01 x02 x12 x14 x23 x27 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((t + ((-1) * x27) + x67) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x27) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x02 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th6872 t x01 x02 x12 x14 x23 x27 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u0 (And.intro u9 (And.intro u4 (And.intro u8 (And.intro u3 (And.intro u1 (And.intro u6 (And.intro u2 u5))))))))))) h

theorem clause13622 (t x01 x15 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ (x57 ≥ 0))) := by
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
  have u3 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x57 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6880 t x01 x15 x45 x56 x57
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u3 (And.intro u6 u4))))))) h

theorem clause13625 (t x01 x04 x05 x13 x37 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + x01 + ((-1) * x04)) ≥ 1)) ∨ (¬ ((t + ((-1) * x37) + x57) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x01 + ((-1) * x04)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x37) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x13 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th6886 t x01 x04 x05 x13 x37 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u1 (And.intro u3 (And.intro u8 (And.intro u0 (And.intro u4 (And.intro u7 (And.intro u2 u5)))))))))) h

theorem clause13628 (t x03 x13 x34 x35 x57 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ (x03 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ ((t + ((-1) * x57)) ≤ 0)) := by
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
  have u3 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x03 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th6915 t x03 x13 x34 x35 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u6 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u2 u5)))))))) h

theorem clause13629 (x01 x02 x04 : ℝ) : (((x01 + ((-1) * x02)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x04)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th6916 x01 x02 x04
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

#print axioms clause13629
end NineCNFDirectTrial
