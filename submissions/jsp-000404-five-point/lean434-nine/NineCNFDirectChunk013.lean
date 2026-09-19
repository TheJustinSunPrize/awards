import NineTheoryTrial

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineCNFDirectTrial

theorem clause14213 (t x03 x05 x13 x35 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((t + x03 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x03 + ((-1) * x13)) ≥ 1) := by
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
  have h := NineTheoryTrial.th8352 t x03 x05 x13 x35 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u1 (And.intro u3 u5))))))) h

theorem clause14214 (t x02 x05 x23 x24 x25 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((t + x23 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x23 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8354 t x02 x05 x23 x24 x25 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u2 (And.intro u6 (And.intro u5 u1)))))))) h

theorem clause14216 (t x01 x04 x07 x12 x13 x24 x36 x47 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((t + x47 + ((-1) * x67)) ≥ 1)) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x07)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x07 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x47 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x07)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th8356 t x01 x04 x07 x12 x13 x24 x36 x47 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u10 (And.intro u7 (And.intro u0 (And.intro u5 (And.intro u9 (And.intro u4 (And.intro u1 (And.intro u6 (And.intro u3 (And.intro u11 u2))))))))))))) h

theorem clause14217 (t x01 x02 x13 x24 x35 x47 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + x47 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x24)) ≥ 1) := by
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
  have u7 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8357 t x01 x02 x13 x24 x35 x47 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u6 (And.intro u5 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u2 u4))))))))) h

theorem clause14218 (t x03 x13 x35 x36 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x56)) ≤ 0)) ∨ (¬ (x03 ≥ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x03 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8361 t x03 x13 x35 x36 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u6 (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u7 (And.intro u1 u5))))))))) h

theorem clause14219 (t x01 x04 x12 x15 x24 x47 x56 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x68) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8362 t x01 x04 x12 x15 x24 x47 x56 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u8 (And.intro u6 (And.intro u0 (And.intro u5 (And.intro u3 (And.intro u2 (And.intro u9 (And.intro u10 (And.intro u1 u4)))))))))))) h

theorem clause14220 (t x03 x13 x34 x35 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ (x03 ≥ 0)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ ((t + ((-1) * x47)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x03 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8363 t x03 x13 x34 x35 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u6 (And.intro u4 (And.intro u3 (And.intro u5 (And.intro u0 u1)))))))) h

theorem clause14221 (t x02 x06 x12 x24 x26 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x06)) ≥ 0)) ∨ (¬ (x26 ≥ 0)) ∨ (¬ ((x26 + ((-1) * x68)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x26 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x26 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8364 t x02 x06 x12 x24 x26 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u6 (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u7 (And.intro u5 u4))))))))) h

theorem clause14222 (t x01 x02 x12 x15 x24 x27 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((t + x27 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x27 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x02 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8365 t x01 x02 x12 x15 x24 x27 x56 x67
  exact (fun hh => (fun hh => hh u9) (hh (And.intro u8 (And.intro u2 (And.intro u6 (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u3 (And.intro u5 u7)))))))))) h

theorem clause14223 (t x01 x03 x07 x13 x36 x37 x47 x78 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x37) + x47) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x07)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x07 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x37) + x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x01 + ((-1) * x07)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8366 t x01 x03 x07 x13 x36 x37 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u4 (And.intro u8 (And.intro u3 (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u7 u6)))))))))) h

theorem clause14224 (t x13 x24 x34 x35 x36 x45 x47 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((t + ((-1) * x34) + x35) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x56)) ≤ 0)) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x34) + x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x36 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8368 t x13 x24 x34 x35 x36 x45 x47 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u1 (And.intro u10 (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u9 (And.intro u7 (And.intro u5 (And.intro u6 u4)))))))))))) h

theorem clause14225 (t x01 x03 x04 x13 x24 x34 x36 x45 x46 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x04)) ≥ 1)) ∨ (¬ (x45 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
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
  have u5 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + x01 + ((-1) * x04)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8369 t x01 x03 x04 x13 x24 x34 x36 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u9 (And.intro u1 (And.intro u4 (And.intro u5 (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u7 (And.intro u10 (And.intro u8 u6)))))))))))) h

theorem clause14226 (t x01 x06 x13 x15 x34 x36 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x06 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((t + ((-1) * x67) + x68) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 + ((-1) * x68)) ≥ 1) := by
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
  have u9 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((t + ((-1) * x67) + x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8370 t x01 x06 x13 x15 x34 x36 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u10 (And.intro u9 (And.intro u0 (And.intro u7 (And.intro u2 (And.intro u8 (And.intro u6 (And.intro u5 (And.intro u4 (And.intro u1 u3)))))))))))) h

theorem clause14227 (x35 x56 x57 : ℝ) : ((¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x57)) ≤ 0)) ∨ ((x35 + ((-1) * x57)) ≤ (-1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x35 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8375 x35 x56 x57
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause14228 (t x02 x03 x27 x35 x56 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x03) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x02) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x68) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8377 t x02 x03 x27 x35 x56 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u2 (And.intro u4 (And.intro u1 (And.intro u0 (And.intro u6 u7))))))))) h

theorem clause14230 (t x02 x04 x05 x24 x35 x45 x48 x56 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x05) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x58)) ≤ 0) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1))) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x04 + ((-1) * x48)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x48)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x02) + x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x58)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x35 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x04 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x24 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8383 t x02 x04 x05 x24 x35 x45 x48 x56 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u6 (And.intro u3 (And.intro u4 (And.intro u1 (And.intro u5 (And.intro u7 (And.intro u0 (And.intro u2 (And.intro u9 u10)))))))))))) h

theorem clause14231 (t x24 x25 x45 : ℝ) : (((t + ((-1) * x24)) ≤ 0) ∨ ((t + x25 + ((-1) * x45)) ≥ 1) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ (x25 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x25 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th8388 t x24 x25 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u2 u3))))) h

theorem clause14233 (t x02 x03 x05 x12 x13 x34 x46 x56 x67 x68 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((t + ((-1) * x67) + x68) ≥ 1))) := by
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
  have u3 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x12) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((t + ((-1) * x67) + x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8390 t x02 x03 x05 x12 x13 x34 x46 x56 x67 x68
  exact (fun hh => (fun hh => hh u9) (hh (And.intro u8 (And.intro u3 (And.intro u6 (And.intro u5 (And.intro u4 (And.intro u2 (And.intro u0 (And.intro u7 (And.intro u10 u1))))))))))) h

theorem clause14234 (t x01 x13 x17 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ ((t + ((-1) * x57)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1)))) := by
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
  have u4 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8393 t x01 x13 x17 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u6 u4)))))))) h

theorem clause14236 (t x15 x45 x57 : ℝ) : (((t + x15 + ((-1) * x45)) ≥ 1) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ ((t + ((-1) * x57)) ≤ 0) ∨ (¬ (x15 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x15 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th8397 t x15 x45 x57
  exact (fun hh => u0 (hh (And.intro u2 (And.intro u3 u1)))) h

theorem clause14237 (t x02 x03 x27 x34 x46 x68 x78 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x02) + x03) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
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
  have u3 : ((t + ((-1) * x02) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x68) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8398 t x02 x03 x27 x34 x46 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u2 (And.intro u7 (And.intro u3 (And.intro u6 (And.intro u1 u0))))))))) h

theorem clause14238 (t x01 x12 x13 x23 x34 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8399 t x01 x12 x13 x23 x34 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u6 (And.intro u0 (And.intro u5 (And.intro u3 (And.intro u4 u7))))))))) h

theorem clause14239 (t x12 x13 x23 x25 x34 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + ((-1) * x23) + x25) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1))) := by
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
  have u4 : ((t + ((-1) * x23) + x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8400 t x12 x13 x23 x25 x34
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u4 (And.intro u2 (And.intro u5 (And.intro u0 u1)))))) h

theorem clause14240 (t x03 x23 x34 x35 x36 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ (x36 ≥ 0)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ ((t + ((-1) * x35)) ≤ 0)) := by
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
  have u3 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x36 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8401 t x03 x23 x34 x35 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u5 (And.intro u2 u6)))))))) h

theorem clause14241 (x03 x13 x36 : ℝ) : (((x03 + ((-1) * x36)) ≤ (-1)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8403 x03 x13 x36
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause14242 (x02 x23 x25 : ℝ) : ((¬ ((x23 + ((-1) * x25)) ≤ 0)) ∨ ((x02 + ((-1) * x25)) ≤ (-1)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x23 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x25)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8405 x02 x23 x25
  exact (fun hh => u1 (hh (And.intro u0 u2))) h

theorem clause14243 (t x01 x02 x07 : ℝ) : ((¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ (¬ ((t + x01 + ((-1) * x07)) ≥ 1)) ∨ ((t + x02 + ((-1) * x07)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x02)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x07)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + x02 + ((-1) * x07)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8407 t x01 x02 x07
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause14244 (t x01 x02 x04 : ℝ) : ((¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ ((t + x02 + ((-1) * x04)) ≥ 1) ∨ (¬ ((t + x01 + ((-1) * x04)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x02)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + x02 + ((-1) * x04)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + x01 + ((-1) * x04)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8409 t x01 x02 x04
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause14245 (t x02 x12 x23 x26 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ (x02 ≥ 0)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
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
  have u3 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8410 t x02 x12 x23 x26 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u6 (And.intro u4 (And.intro u1 (And.intro u2 u3)))))))) h

theorem clause14246 (x13 x23 x36 : ℝ) : ((¬ ((x13 + ((-1) * x23)) ≥ 0)) ∨ ((x23 + ((-1) * x36)) ≤ (-1)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x13 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8414 x13 x23 x36
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause14247 (t x04 x34 x45 x46 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ ((t + ((-1) * x46)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ (x45 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8420 t x04 x34 x45 x46 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u3 (And.intro u6 (And.intro u4 u1)))))))) h

theorem clause14249 (t x15 x25 x45 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x25 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x25)) ≥ 0))) := by
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
  have u5 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8429 t x15 x25 x45 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u6 (And.intro u2 (And.intro u0 (And.intro u4 u1)))))))) h

theorem clause14250 (t x01 x04 x06 x12 x25 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x04) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x46) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x01) + x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8430 t x01 x04 x06 x12 x25 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u8 (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u7 (And.intro u6 (And.intro u3 u4)))))))))) h

theorem clause14252 (t x01 x04 x13 x35 x46 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x04) ≥ 1)) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1))) := by
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
  have u4 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x01) + x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8437 t x01 x04 x13 x35 x46 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u7 (And.intro u0 (And.intro u2 (And.intro u5 (And.intro u6 u4))))))))) h

theorem clause14254 (t x03 x13 x34 x35 x37 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ ((t + ((-1) * x35)) ≤ 0) ∨ (¬ (x34 ≥ 0)) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x34)) ≥ 1) := by
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
  have u4 : ¬ ((t + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8439 t x03 x13 x34 x35 x37
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u6 (And.intro u3 (And.intro u4 (And.intro u1 u2)))))))) h

theorem clause14255 (x35 x36 x57 x67 : ℝ) : ((¬ ((x35 + ((-1) * x36)) ≥ 0)) ∨ ((x35 + ((-1) * x57)) ≥ 1) ∨ (¬ ((x57 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x57 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th8446 x35 x36 x57 x67
  exact (fun hh => u1 (hh (And.intro u3 (And.intro u0 u2)))) h

theorem clause14258 (t x04 x45 x47 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ (x57 ≥ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x57 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8452 t x04 x45 x47 x57 x78
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u3 (And.intro u5 (And.intro u2 (And.intro u1 (And.intro u4 u0))))))) h

theorem clause14259 (t x03 x13 x23 x34 x36 x67 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8453 t x03 x13 x23 x34 x36 x67
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u0 (And.intro u6 (And.intro u3 (And.intro u2 (And.intro u7 (And.intro u1 u4)))))))) h

theorem clause14260 (t x07 x25 x47 x56 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x57)) ≥ 0)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ ((t + ((-1) * x47)) ≤ 0) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x07 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8454 t x07 x25 x47 x56 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u7 (And.intro u6 u5))))))))) h

theorem clause14262 (t x03 x34 x45 x56 x68 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x68)) ≤ 0) ∨ (¬ (x03 ≥ 0)) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1)))) := by
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
  have u3 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x03 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8462 t x03 x34 x45 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u4 (And.intro u1 u6)))))))) h

theorem clause14265 (t x01 x13 x23 x34 x35 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ ((t + ((-1) * x35)) ≤ 0) ∨ (¬ (x01 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8470 t x01 x13 x23 x34 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u5 (And.intro u6 u1)))))))) h

theorem clause14266 (t x01 x02 x14 x23 x24 x47 x48 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ ((t + ((-1) * x47)) ≤ 0) ∨ (¬ ((x14 + ((-1) * x48)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x48)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x02)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x14 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x24 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8476 t x01 x02 x14 x23 x24 x47 x48
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u6 (And.intro u2 (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u0 (And.intro u3 u8)))))))))) h

theorem clause14267 (t x01 x14 x34 x46 x48 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ ((t + ((-1) * x46)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x14 + ((-1) * x48)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x48)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8477 t x01 x14 x34 x46 x48
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6)))))))) h

theorem clause14269 (t x07 x36 x56 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((t + ((-1) * x36) + x56) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x57)) ≤ 0)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x07 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x07 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x36) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8481 t x07 x36 x56 x57 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u4 (And.intro u3 (And.intro u5 (And.intro u0 (And.intro u1 u6)))))))) h

theorem clause14270 (x16 x67 x68 : ℝ) : ((¬ ((x16 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x68)) ≤ 0)) ∨ (¬ ((x16 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x67 + ((-1) * x68)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x16 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8484 x16 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 u2)))) h

theorem clause14272 (t x03 x13 x34 x37 x78 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ (x03 ≥ 0)) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
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
  have u3 : (x03 ≥ 0) := by
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
  have h := NineTheoryTrial.th8489 t x03 x13 x34 x37 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u3 (And.intro u4 (And.intro u2 (And.intro u0 u6)))))))) h

theorem clause14273 (t x01 x05 x12 x24 x48 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x05)) ≥ 1)) ∨ (¬ ((t + ((-1) * x48) + x78) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x48)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x01 + ((-1) * x05)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x48) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x24 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8490 t x01 x05 x12 x24 x48 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u7 (And.intro u2 u6))))))))) h

theorem clause14274 (t x04 x34 x36 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((t + x04 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x04 + ((-1) * x34)) ≥ 1) := by
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
  have h := NineTheoryTrial.th8492 t x04 x34 x36 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u5 (And.intro u1 u3))))))) h

theorem clause14275 (x23 x34 x36 : ℝ) : (((x23 + ((-1) * x34)) ≤ (-1)) ∨ (¬ ((x34 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x34)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8494 x23 x34 x36
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause14276 (t x06 x12 x24 x26 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x24)) ≤ 0) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1)) ∨ (¬ (x06 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x06 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8496 t x06 x12 x24 x26 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u5 (And.intro u2 u4)))))))) h

theorem clause14277 (t x01 x02 x04 x12 x23 x24 x45 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ ((t + ((-1) * x24)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((t + x01 + ((-1) * x04)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x02)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x01 + ((-1) * x04)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8497 t x01 x02 x04 x12 x23 x24 x45 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u10 (And.intro u0 (And.intro u9 (And.intro u4 (And.intro u8 (And.intro u3 (And.intro u6 (And.intro u1 (And.intro u2 (And.intro u5 u7)))))))))))) h

theorem clause14278 (t x01 x04 x12 x23 x34 x45 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((t + x01 + ((-1) * x04)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
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
  have u3 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x01 + ((-1) * x04)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8498 t x01 x04 x12 x23 x34 x45 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u9 (And.intro u0 (And.intro u8 (And.intro u5 (And.intro u7 (And.intro u3 (And.intro u6 (And.intro u4 (And.intro u2 u1))))))))))) h

theorem clause14279 (t x04 x36 x45 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x36)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x45 ≥ 0))) := by
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
  have u3 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th8500 t x04 x36 x45 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u5 (And.intro u4 (And.intro u2 (And.intro u0 u6)))))))) h

theorem clause14280 (t x01 x02 x15 x23 x34 x46 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x01) + x02) ≥ 1) := by
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
  have u5 : ((t + ((-1) * x46) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8501 t x01 x02 x15 x23 x34 x46 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u3 (And.intro u6 (And.intro u2 (And.intro u7 (And.intro u0 u4))))))))) h

theorem clause14281 (t x01 x03 x12 x13 x15 x16 x23 x34 x36 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ ((t + x16 + ((-1) * x36)) ≥ 1))) := by
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
  have u3 : ((x12 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x12 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + x16 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8502 t x01 x03 x12 x13 x15 x16 x23 x34 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u6 (And.intro u0 (And.intro u4 (And.intro u9 (And.intro u2 (And.intro u3 (And.intro u5 (And.intro u7 u8))))))))))) h

theorem clause14282 (t x01 x03 x15 x23 x34 x36 x56 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + ((-1) * x36) + x56) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
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
  have u3 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x36) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8503 t x01 x03 x15 x23 x34 x36 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u1 (And.intro u3 (And.intro u6 (And.intro u4 (And.intro u7 u0))))))))) h

theorem clause14283 (t x01 x02 x12 x15 x16 x23 x34 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((t + x16 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + x12 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
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
  have u5 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x16 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x12 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8504 t x01 x02 x12 x15 x16 x23 x34 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u5 (And.intro u7 (And.intro u1 (And.intro u3 (And.intro u0 (And.intro u8 (And.intro u4 u2)))))))))) h

theorem clause14284 (t x02 x04 x26 x36 x45 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x02 + ((-1) * x04)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + ((-1) * x36) + x56) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x02 + ((-1) * x04)) ≥ 1) := by
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
  have u5 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8508 t x02 x04 x26 x36 x45 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u5 (And.intro u2 (And.intro u1 (And.intro u7 (And.intro u4 (And.intro u3 u0))))))))) h

theorem clause14286 (t x02 x12 x15 x23 x37 x45 x57 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x58)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((t + ((-1) * x37) + x57) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x58)) ≥ 1))) := by
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
  have u3 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x12 + ((-1) * x15)) ≥ 1) := by
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
  have u8 : ((x15 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8514 t x02 x12 x15 x23 x37 x45 x57 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u1 (And.intro u5 (And.intro u7 u8)))))))))) h

theorem clause14287 (t x05 x36 x56 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + ((-1) * x36) + x56) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x36) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x57 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8516 t x05 x36 x56 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u4 (And.intro u1 (And.intro u3 u0))))))) h

theorem clause14288 (t x07 x15 x36 x56 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x07 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((t + ((-1) * x36) + x56) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x57)) ≥ 0)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x07 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x36) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8517 t x07 x15 x36 x56 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u4 (And.intro u5 (And.intro u3 u6)))))))) h

theorem clause14289 (t x01 x03 x15 x34 x47 x58 x78 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + x58 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x58)) ≥ 1))) := by
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
  have u3 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
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
  have u6 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x15 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8521 t x01 x03 x15 x34 x47 x58 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u4 (And.intro u5 (And.intro u7 (And.intro u3 (And.intro u6 u1))))))))) h

theorem clause14290 (t x01 x03 x04 x12 x26 x34 x46 x48 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((t + x26 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x48)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x48)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x26 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x04 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x34 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8522 t x01 x03 x04 x12 x26 x34 x46 x48
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u4 (And.intro u8 (And.intro u0 (And.intro u5 u6)))))))))) h

theorem clause14291 (t x01 x03 x15 x34 x48 x57 x78 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((t + ((-1) * x48) + x78) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x48)) ≤ (-1)))) := by
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
  have u3 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x48) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x34 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8525 t x01 x03 x15 x34 x48 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u7 (And.intro u3 (And.intro u5 (And.intro u1 u6))))))))) h

theorem clause14292 (t x01 x02 x03 x12 x17 x34 x48 x78 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((t + ((-1) * x02) + x03) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + ((-1) * x48) + x78) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x48)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x02) + x03) ≥ 1) := by
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
  have u7 : ((t + ((-1) * x48) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x34 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8527 t x01 x02 x03 x12 x17 x34 x48 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u7 (And.intro u1 (And.intro u3 (And.intro u5 (And.intro u6 (And.intro u2 u8)))))))))) h

theorem clause14293 (t x03 x06 x12 x16 x23 x25 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x23 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x16)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x23 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x23)) ≥ 0) := by
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
  have u5 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th8528 t x03 x06 x12 x16 x23 x25 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u6 (And.intro u5 u7))))))))) h

theorem clause14294 (t x02 x03 x13 x23 x24 x26 x35 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((t + x23 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((t + x26 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x23 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x26 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8531 t x02 x03 x13 x23 x24 x26 x35 x36
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u6 (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u7 (And.intro u8 (And.intro u0 u5))))))))) h

theorem clause14295 (t x04 x14 x16 x35 x36 x48 x67 : ℝ) : ((¬ ((x35 + ((-1) * x36)) ≥ 0)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x14 + ((-1) * x16)) ≤ 0)) ∨ ((t + ((-1) * x35)) ≤ 0) ∨ (¬ (x04 ≥ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x48)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x48)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x04 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x14 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x04 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8532 t x04 x14 x16 x35 x36 x48 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u4 (And.intro u0 (And.intro u1 (And.intro u8 (And.intro u2 (And.intro u7 (And.intro u5 u3)))))))))) h

theorem clause14296 (t x01 x13 x34 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8535 t x01 x13 x34 x47 x78
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u2 (And.intro u1 (And.intro u4 (And.intro u6 (And.intro u0 u3))))))) h

theorem clause14297 (t x01 x05 x13 x34 x48 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x05)) ≥ 1)) ∨ (¬ ((t + ((-1) * x48) + x78) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x48)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x01 + ((-1) * x05)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x48) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x34 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8536 t x01 x05 x13 x34 x48 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u3 (And.intro u4 (And.intro u2 (And.intro u1 (And.intro u7 u6))))))))) h

theorem clause14299 (t x03 x12 x23 x34 x47 x78 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0)) := by
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
  have u4 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8540 t x03 x12 x23 x34 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u1 (And.intro u5 (And.intro u0 (And.intro u2 (And.intro u3 (And.intro u6 u4))))))))) h

theorem clause14300 (t x02 x04 x06 x24 x36 x45 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((t + ((-1) * x36) + x46) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x02) + x06) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
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
  have u4 : ((x02 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x36) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x02) + x06) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8542 t x02 x04 x06 x24 x36 x45 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u6 (And.intro u0 (And.intro u7 (And.intro u1 (And.intro u4 (And.intro u2 (And.intro u5 u3)))))))))) h

theorem clause14301 (x35 x36 x37 : ℝ) : ((¬ ((x35 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x36 + ((-1) * x37)) ≥ 0)) ∨ ((x35 + ((-1) * x37)) ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x36 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x35 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8544 x35 x36 x37
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause14302 (t x02 x04 x12 x24 x48 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x02 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x48)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x48)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x02 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8547 t x02 x04 x12 x24 x48
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u5 (And.intro u2 u4))))))) h

theorem clause14303 (t x03 x24 x34 x47 x48 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ (x03 ≥ 0)) ∨ ((t + ((-1) * x47)) ≤ 0) ∨ (¬ ((x24 + ((-1) * x48)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x48)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8549 t x03 x24 x34 x47 x48
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u1 (And.intro u2 (And.intro u3 (And.intro u0 u6)))))))) h

theorem clause14305 (t x04 x06 x45 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x45 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x45 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8554 t x04 x06 x45 x46 x67
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u1 (And.intro u4 (And.intro u2 (And.intro u0 u5)))))) h

theorem clause14307 (t x02 x03 x05 x23 x24 x26 x35 x56 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((t + x23 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x58)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((t + x26 + ((-1) * x56)) ≥ 1))) := by
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
  have u3 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x05 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + x26 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8557 t x02 x03 x05 x23 x24 x26 x35 x56 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u6 (And.intro u7 (And.intro u8 (And.intro u0 (And.intro u9 (And.intro u1 (And.intro u2 (And.intro u3 u5))))))))))) h

theorem clause14308 (t x01 x02 x12 x13 x24 x26 x35 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((t + x26 + ((-1) * x56)) ≥ 1)) ∨ (¬ (x01 ≥ 0))) := by
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
  have u3 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x26 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8559 t x01 x02 x12 x13 x24 x26 x35 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u9 (And.intro u2 (And.intro u3 (And.intro u7 (And.intro u8 (And.intro u1 (And.intro u5 u6))))))))))) h

theorem clause14309 (t x01 x13 x35 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ ((t + ((-1) * x78)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8560 t x01 x13 x35 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u5 (And.intro u1 (And.intro u6 (And.intro u4 u3)))))))) h

theorem clause14310 (t x01 x04 x13 x35 x47 x58 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + x01 + ((-1) * x04)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x58) + x78) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x01 + ((-1) * x04)) ≥ 1) := by
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
  have h := NineTheoryTrial.th8561 t x01 x04 x13 x35 x47 x58 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u7 (And.intro u5 (And.intro u4 u6))))))))) h

theorem clause14311 (t x02 x24 x26 x27 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((t + x26 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x27)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x26 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 + ((-1) * x27)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8562 t x02 x24 x26 x27 x36 x67
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u4 (And.intro u1 (And.intro u2 (And.intro u5 (And.intro u0 u3))))))) h

theorem clause14312 (t x03 x12 x23 x35 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0)) := by
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
  have u3 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x12 ≥ 0) := by
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
  have h := NineTheoryTrial.th8563 t x03 x12 x23 x35 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u7 (And.intro u1 (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u3 u6))))))))) h

theorem clause14314 (t x02 x26 x28 x56 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((t + x26 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x28 + ((-1) * x68)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x28)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x26 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x28 + ((-1) * x68)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x28)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8566 t x02 x26 x28 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u0 (And.intro u1 (And.intro u2 u4))))))) h

theorem clause14315 (t x02 x03 x23 x24 x28 x35 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((t + x23 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + x28 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x28)) ≥ 1))) := by
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
  have u3 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
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
  have u7 : ((t + x28 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x02 + ((-1) * x28)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8567 t x02 x03 x23 x24 x28 x35 x57 x78
  exact (fun hh => (fun hh => hh u8) (hh (And.intro u2 (And.intro u6 (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u7 (And.intro u3 u1))))))))) h

theorem clause14316 (t x23 x34 x36 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((t + x45 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x34)) ≥ 1) := by
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
  have u5 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8568 t x23 x34 x36 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u5 (And.intro u3 u2))))))) h

theorem clause14317 (t x04 x23 x34 x45 x56 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ (x68 ≥ 0)) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x68 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8569 t x04 x23 x34 x45 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u6 (And.intro u7 (And.intro u3 u2))))))))) h

theorem clause14318 (t x01 x02 x12 x14 x15 x23 x37 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((t + ((-1) * x37) + x57) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
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
  have u3 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
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
  have u6 : ((x15 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x37) + x57) ≥ 1) := by
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
  have h := NineTheoryTrial.th8576 t x01 x02 x12 x14 x15 x23 x37 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u7 (And.intro u9 (And.intro u3 (And.intro u0 (And.intro u8 (And.intro u4 (And.intro u5 (And.intro u2 u1))))))))))) h

theorem clause14319 (x03 x06 x37 x67 : ℝ) : ((¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x37 + ((-1) * x67)) ≥ 0)) ∨ ((x03 + ((-1) * x37)) ≤ (-1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x37 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((x03 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th8578 x03 x06 x37 x67
  exact (fun hh => u3 (hh (And.intro u2 (And.intro u0 u1)))) h

theorem clause14322 (t x01 x02 x03 x04 x13 x23 x35 x38 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x04)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((t + ((-1) * x38) + x78) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x38)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x02)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x03)) ≤ 0) := by
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
  have u7 : ((t + x01 + ((-1) * x04)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x38) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x23 + ((-1) * x38)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8583 t x01 x02 x03 x04 x13 x23 x35 x38 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u10 (And.intro u5 (And.intro u7 (And.intro u6 (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u1 (And.intro u8 u9)))))))))))) h

theorem clause14324 (x16 x26 x67 : ℝ) : (((x26 + ((-1) * x67)) ≥ 1) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x26)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x16 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8586 x16 x26 x67
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause14325 (t x02 x03 x13 x16 x35 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ (x02 ≥ 0)) ∨ ((t + ((-1) * x36)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x16)) ≤ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
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
  have u4 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x13 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8587 t x02 x03 x13 x16 x35 x36 x67
  exact (fun hh => (fun hh => hh u8) (hh (And.intro u4 (And.intro u7 (And.intro u6 (And.intro u0 (And.intro u2 (And.intro u5 (And.intro u1 u3))))))))) h

theorem clause14326 (t x01 x06 x12 x16 x25 x46 x58 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((t + ((-1) * x58) + x68) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1)) ∨ ((t + ((-1) * x16)) ≤ 0) ∨ (¬ ((x25 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x58) + x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ¬ ((t + ((-1) * x16)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x25 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8590 t x01 x06 x12 x16 x25 x46 x58 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u9 (And.intro u6 (And.intro u5 (And.intro u8 (And.intro u0 (And.intro u1 (And.intro u10 (And.intro u2 (And.intro u4 u3)))))))))))) h

theorem clause14327 (t x02 x23 x37 x56 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ (x02 ≥ 0)) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x56 + ((-1) * x57)) ≥ 0)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8591 t x02 x23 x37 x56 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u4 (And.intro u0 (And.intro u6 (And.intro u1 (And.intro u5 (And.intro u7 u3))))))))) h

theorem clause14328 (t x02 x04 x12 x13 x23 x24 x35 x46 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((t + x02 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((t + x46 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1))) := by
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
  have u4 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x46 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8592 t x02 x04 x12 x13 x23 x24 x35 x46 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u6 (And.intro u9 (And.intro u7 (And.intro u8 (And.intro u4 (And.intro u5 u1))))))))))) h

theorem clause14330 (t x01 x02 x13 x27 x35 x58 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x58) + x78) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
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
  have u6 : ((x02 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8596 t x01 x02 x13 x27 x35 x58 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u7 (And.intro u6 u3))))))))) h

theorem clause14332 (t x01 x14 x34 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ ((t + ((-1) * x46)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ (x01 ≥ 0))) := by
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
  have u3 : ¬ ((t + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8600 t x01 x14 x34 x45 x46
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u1 (And.intro u3 (And.intro u6 (And.intro u0 (And.intro u2 u4))))))) h

theorem clause14335 (t x02 x04 x26 x34 x36 x46 x47 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ (x02 ≥ 0)) ∨ (¬ ((t + ((-1) * x36) + x46) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x36) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x46)) ≥ 1) := by
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
  have u8 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8608 t x02 x04 x26 x34 x36 x46 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u8 (And.intro u4 (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u9 (And.intro u6 u7))))))))))) h

theorem clause14336 (t x01 x03 x14 x23 x35 x36 x46 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x36) + x46) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x36) + x46) ≥ 1) := by
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
  have u7 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8612 t x01 x03 x14 x23 x35 x36 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u6 (And.intro u7 (And.intro u3 (And.intro u2 (And.intro u1 u0))))))))) h

theorem clause14337 (t x01 x03 x04 x14 x23 x34 x35 x47 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + x14 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x04)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + x14 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x35)) ≥ 1) := by
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
  have u7 : ((x14 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8613 t x01 x03 x04 x14 x23 x34 x35 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u7 (And.intro u5 (And.intro u8 (And.intro u6 (And.intro u2 u3)))))))))) h

theorem clause14338 (x24 x34 x46 : ℝ) : ((¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x34)) ≤ 0)) ∨ ((x24 + ((-1) * x46)) ≤ (-1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x24 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8614 x24 x34 x46
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause14339 (t x03 x23 x34 x35 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ ((t + ((-1) * x46)) ≤ 0) ∨ (¬ (x03 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
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
  have u5 : ¬ ((t + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x03 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8617 t x03 x23 x34 x35 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u4 (And.intro u6 (And.intro u5 (And.intro u3 u2)))))))) h

theorem clause14340 (t x03 x12 x23 x34 x45 x56 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ (x12 ≥ 0))) := by
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
  have u3 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8619 t x03 x12 x23 x34 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u6 (And.intro u1 (And.intro u3 (And.intro u0 (And.intro u7 (And.intro u4 u2))))))))) h

theorem clause14341 (t x01 x03 x12 x26 x34 x45 x56 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + x26 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
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
  have u3 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x26 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8620 t x01 x03 x12 x26 x34 x45 x56
  exact (fun hh => (fun hh => hh u7) (hh (And.intro u4 (And.intro u2 (And.intro u5 (And.intro u0 (And.intro u1 (And.intro u6 u3)))))))) h

theorem clause14342 (x04 x45 x46 : ℝ) : (((x04 + ((-1) * x45)) ≥ 1) ∨ (¬ ((x45 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8622 x04 x45 x46
  exact (fun hh => u0 (hh (And.intro u2 u1))) h

theorem clause14343 (t x02 x03 x04 x24 x35 x45 x48 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ (x45 ≥ 0)) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x48)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x48)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x02) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
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
  have u5 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x04 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x24 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8623 t x02 x03 x04 x24 x35 x45 x48 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u8 (And.intro u6 (And.intro u5 (And.intro u7 (And.intro u1 (And.intro u3 (And.intro u9 (And.intro u10 u4)))))))))))) h

theorem clause14344 (t x02 x03 x24 x35 x48 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + x48 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x48)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x02) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x24)) ≥ 1) := by
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
  have u6 : ((t + x48 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x24 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8627 t x02 x03 x24 x35 x48 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u6 (And.intro u7 u5))))))))) h

theorem clause14345 (t x14 x24 x34 : ℝ) : ((¬ ((x14 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((t + x24 + ((-1) * x34)) ≥ 1)) ∨ ((t + ((-1) * x14) + x24) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x14 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((t + x24 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x14) + x24) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8629 t x14 x24 x34
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause14346 (t x03 x04 x23 x34 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + x03 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x03 + ((-1) * x23)) ≥ 1) := by
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
  have h := NineTheoryTrial.th8631 t x03 x04 x23 x34 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u2 u4))))))) h

theorem clause14347 (x03 x13 x37 : ℝ) : ((¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ ((x13 + ((-1) * x37)) ≤ (-1)) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8640 x03 x13 x37
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause14349 (t x01 x02 x15 x23 x35 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
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
  have u4 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x56) + x57) ≥ 1) := by
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
  have h := NineTheoryTrial.th8645 t x01 x02 x15 x23 x35 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u6 (And.intro u0 (And.intro u7 (And.intro u1 (And.intro u2 (And.intro u3 u4))))))))) h

theorem clause14350 (t x13 x14 x23 x34 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((t + x13 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x13 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8647 t x13 x14 x23 x34 x45
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u2 u3)))))) h

theorem clause14351 (t x05 x24 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x24)) ≤ 0) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8652 t x05 x24 x45 x56 x57
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u3 (And.intro u4 (And.intro u1 (And.intro u6 (And.intro u2 u0))))))) h

theorem clause14352 (t x04 x24 x25 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x04 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x04 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8653 t x04 x24 x25 x45 x57
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u5 u2)))))) h

theorem clause14354 (t x01 x02 x16 x23 x35 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
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
  have u4 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x57) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8664 t x01 x02 x16 x23 x35 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u7 (And.intro u4 (And.intro u2 (And.intro u1 (And.intro u5 (And.intro u0 u3))))))))) h

theorem clause14357 (t x01 x02 x12 x16 x17 x23 x35 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + x17 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + x12 + ((-1) * x16)) ≥ 1))) := by
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
  have u4 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x17 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x12 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8669 t x01 x02 x12 x16 x17 x23 x35 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u7 (And.intro u6 (And.intro u8 (And.intro u1 (And.intro u2 (And.intro u5 (And.intro u0 u3)))))))))) h

theorem clause14358 (t x02 x04 x07 x24 x45 x47 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x47) + x67) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + x02 + ((-1) * x07)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x07 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x47) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x02 + ((-1) * x07)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8671 t x02 x04 x07 x24 x45 x47 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u8 (And.intro u0 (And.intro u6 (And.intro u4 (And.intro u7 (And.intro u3 (And.intro u1 u5)))))))))) h

theorem clause14359 (t x01 x03 x04 x12 x26 x34 x45 x46 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + x26 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x26 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8674 t x01 x03 x04 x12 x26 x34 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u7 (And.intro u5 (And.intro u3 (And.intro u1 (And.intro u6 (And.intro u4 (And.intro u2 u0)))))))))) h

theorem clause14360 (t x03 x04 x12 x23 x34 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ ((t + ((-1) * x46)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ (x12 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8675 t x03 x04 x12 x23 x34 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u6 (And.intro u7 (And.intro u1 (And.intro u3 (And.intro u5 (And.intro u4 (And.intro u2 u8)))))))))) h

theorem clause14361 (x05 x35 x56 : ℝ) : ((¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x35)) ≤ 0)) ∨ ((x05 + ((-1) * x56)) ≤ (-1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x05 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8676 x05 x35 x56
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause14363 (t x03 x13 x23 x34 x36 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8682 t x03 x13 x23 x34 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u6 u0)))))))) h

theorem clause14364 (t x02 x03 x25 x34 x47 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((t + x02 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x47 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x02 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x47 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8683 t x02 x03 x25 x34 x47 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u6 (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u7 (And.intro u3 u5))))))))) h

theorem clause14365 (t x03 x34 x37 x45 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + x45 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x47)) ≤ 0))) := by
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
  have u3 : ((t + x45 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 + ((-1) * x47)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8686 t x03 x34 x37 x45 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u5 (And.intro u3 (And.intro u4 u0))))))) h

theorem clause14366 (t x05 x06 x25 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x05 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x05 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8690 t x05 x06 x25 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u4 (And.intro u3 u5))))))) h

theorem clause14367 (t x02 x05 x12 x25 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x02 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x02 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8691 t x02 x05 x12 x25 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u4 (And.intro u5 u2))))))) h

theorem clause14368 (t x01 x03 x12 x26 x37 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x26 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x68) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8693 t x01 x03 x12 x26 x37 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u5 (And.intro u1 (And.intro u6 (And.intro u0 (And.intro u7 u3))))))))) h

theorem clause14369 (t x17 x34 x46 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ (x46 ≥ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ ((t + ((-1) * x17)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8694 t x17 x34 x46 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u4 (And.intro u3 (And.intro u2 (And.intro u1 u6)))))))) h

theorem clause14370 (t x05 x06 x07 x25 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x05 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x05 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x07)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x05 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8695 t x05 x06 x07 x25 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u2 (And.intro u5 (And.intro u3 (And.intro u6 u0)))))))) h

theorem clause14371 (x26 x56 x67 : ℝ) : (((x56 + ((-1) * x67)) ≥ 1) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x56)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x26 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8697 x26 x56 x67
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause14372 (t x02 x03 x12 x25 x26 x34 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((t + x02 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + ((-1) * x26) + x46) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x02 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x26) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8698 t x02 x03 x12 x25 x26 x34 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u4 (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u6 u7))))))))) h

theorem clause14373 (t x01 x12 x13 x23 x25 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x23) + x25) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x23)) ≤ 0) := by
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
  have u4 : ((t + ((-1) * x23) + x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8699 t x01 x12 x13 x23 x25
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u3 (And.intro u1 (And.intro u4 u5))))))) h

theorem clause14374 (t x02 x12 x16 x23 x26 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ (x02 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x16)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th8700 t x02 x12 x16 x23 x26 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u0 (And.intro u4 (And.intro u6 (And.intro u2 (And.intro u1 u7))))))))) h

theorem clause14375 (t x02 x06 x12 x26 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x02 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
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
  have u3 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8701 t x02 x06 x12 x26 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u2 (And.intro u3 (And.intro u0 u1))))))) h

theorem clause14376 (t x01 x12 x16 x26 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x26)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x16 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8702 t x01 x12 x16 x26 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u6 (And.intro u5 (And.intro u2 (And.intro u7 (And.intro u1 u3))))))))) h

theorem clause14377 (t x01 x12 x25 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ (x01 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8704 t x01 x12 x25 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u6 (And.intro u0 (And.intro u2 (And.intro u3 (And.intro u4 u5)))))))) h

theorem clause14378 (t x02 x12 x25 x26 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x02 ≥ 0)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x26 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
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
  have u4 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8705 t x02 x12 x25 x26 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u1 (And.intro u5 (And.intro u6 u7))))))))) h

theorem clause14379 (t x06 x12 x23 x26 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x06 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1)) ∨ (¬ (x06 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x06 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8706 t x06 x12 x23 x26 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u5 u4)))))))) h

theorem clause14380 (t x02 x12 x15 x23 x25 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ (x02 ≥ 0)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x15)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8707 t x02 x12 x15 x23 x25 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u5 (And.intro u3 (And.intro u6 (And.intro u4 (And.intro u0 (And.intro u1 u2))))))))) h

theorem clause14381 (t x01 x03 x15 x34 x47 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x47 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x47 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8708 t x01 x03 x15 x34 x47 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u5 (And.intro u0 (And.intro u1 (And.intro u7 (And.intro u4 (And.intro u3 u2))))))))) h

theorem clause14382 (t x01 x04 x15 x34 x45 x47 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((t + x01 + ((-1) * x04)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x01 + ((-1) * x04)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8709 t x01 x04 x15 x34 x45 x47 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u9 (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u7 (And.intro u6 u8))))))))))) h

theorem clause14383 (t x01 x02 x06 x12 x13 x17 x26 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + x17 + ((-1) * x67)) ≥ 1))) := by
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
  have u3 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x26 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + x17 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8712 t x01 x02 x06 x12 x13 x17 x26 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u9 (And.intro u5 (And.intro u8 (And.intro u0 (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u1 (And.intro u6 u7))))))))))) h

theorem clause14384 (t x01 x02 x12 x13 x17 x25 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + x17 + ((-1) * x67)) ≥ 1))) := by
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
  have u3 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x17 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8714 t x01 x02 x12 x13 x17 x25 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u8 (And.intro u7 (And.intro u3 (And.intro u6 (And.intro u0 (And.intro u2 (And.intro u5 u1)))))))))) h

theorem clause14385 (t x02 x03 x05 x25 x34 x46 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + x02 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + x46 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x02 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x46 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8715 t x02 x03 x05 x25 x34 x46 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u6 (And.intro u7 (And.intro u8 u3)))))))))) h

theorem clause14386 (t x01 x02 x12 x13 x14 x25 x46 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((t + x46 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1)))) := by
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
  have u3 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x46 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8716 t x01 x02 x12 x13 x14 x25 x46 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u7 (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u8 u4)))))))))) h

theorem clause14387 (t x12 x13 x14 : ℝ) : ((¬ ((x13 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ ((t + x12 + ((-1) * x14)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x13 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((t + x12 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + x12 + ((-1) * x14)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8717 t x12 x13 x14
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause14388 (t x01 x02 x05 x12 x13 x17 x25 x37 x47 x57 x58 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x25 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x58)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x37)) ≥ 0)) ∨ ((t + ((-1) * x57)) ≤ 0) ∨ (¬ ((x37 + ((-1) * x47)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ (x78 ≥ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
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
  have u3 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x17 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x37 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))))
  have u12 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))))
  have u13 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))))
  have h := NineTheoryTrial.th8719 t x01 x02 x05 x12 x13 x17 x25 x37 x47 x57 x58 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u12 (And.intro u13 (And.intro u7 (And.intro u11 (And.intro u10 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u9 (And.intro u4 (And.intro u6 u5))))))))))))))) h

theorem clause14389 (t x01 x02 x12 x13 x17 x25 x37 x47 x58 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x58) + x78) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x37 + ((-1) * x47)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x58)) ≤ (-1)))) := by
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
  have u3 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x58) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x37 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x25 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8720 t x01 x02 x12 x13 x17 x25 x37 x47 x58 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u7 (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u0 (And.intro u6 (And.intro u9 (And.intro u8 (And.intro u2 u10)))))))))))) h

theorem clause14390 (t x02 x12 x14 x25 x34 x45 x48 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x14 + ((-1) * x48)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x48)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
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
  have u6 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x14 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x34 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8722 t x02 x12 x14 x25 x34 x45 x48 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u8 (And.intro u0 (And.intro u3 (And.intro u5 (And.intro u1 (And.intro u6 (And.intro u4 (And.intro u2 (And.intro u10 u9)))))))))))) h

theorem clause14391 (t x02 x03 x25 x34 x48 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((t + x02 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + x48 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x48)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x02 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x48 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x34 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8723 t x02 x03 x25 x34 x48 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u6 (And.intro u2 (And.intro u4 (And.intro u0 (And.intro u7 u1))))))))) h

theorem clause14392 (t x01 x02 x12 x13 x16 x26 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x67) + x68) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x68)) ≥ 1))) := by
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
  have u3 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x16)) ≥ 1) := by
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
  have u7 : ((t + ((-1) * x67) + x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x16 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8725 t x01 x02 x12 x13 x16 x26 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u2 (And.intro u6 (And.intro u0 (And.intro u7 (And.intro u8 (And.intro u1 u4)))))))))) h

theorem clause14393 (t x01 x02 x05 x12 x13 x14 x25 x34 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x14 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((t + ((-1) * x25) + x45) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x12 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x25) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8726 t x01 x02 x05 x12 x13 x14 x25 x34 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u6 (And.intro u2 (And.intro u4 (And.intro u10 (And.intro u3 (And.intro u8 (And.intro u0 (And.intro u9 (And.intro u1 u5)))))))))))) h

theorem clause14395 (t x01 x02 x12 x14 x17 x27 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + x17 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1)))) := by
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
  have u4 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x17 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x27 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8728 t x01 x02 x12 x14 x17 x27 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u4 (And.intro u5 (And.intro u7 (And.intro u8 (And.intro u6 u1)))))))))) h

theorem clause14396 (t x02 x03 x05 x26 x34 x48 x56 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + x02 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + x48 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x48)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x02 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
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
  have u9 : ((x34 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8729 t x02 x03 x05 x26 x34 x48 x56 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u8 (And.intro u2 (And.intro u7 (And.intro u3 (And.intro u6 (And.intro u4 (And.intro u5 u9))))))))))) h

theorem clause14397 (t x02 x05 x12 x14 x26 x34 x45 x48 x56 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x45 ≥ 0)) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x48)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x48)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x14 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))))
  have u12 : ((x34 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))))
  have h := NineTheoryTrial.th8730 t x02 x05 x12 x14 x26 x34 x45 x48 x56 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u8 (And.intro u3 (And.intro u7 (And.intro u5 (And.intro u6 (And.intro u10 (And.intro u9 (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u12 u11)))))))))))))) h

theorem clause14398 (t x01 x02 x12 x13 x17 x26 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1))) := by
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
  have u3 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x68)) ≤ (-1)) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x68) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8731 t x01 x02 x12 x13 x17 x26 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u8 (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u7 u6)))))))))) h

theorem clause14399 (t x02 x04 x05 x12 x14 x25 x34 x45 x47 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1))) ∨ ((t + ((-1) * x57)) ≤ 0) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x05)) ≤ 0) := by
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
  have u7 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))))
  have u12 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))))
  have h := NineTheoryTrial.th8732 t x02 x04 x05 x12 x14 x25 x34 x45 x47 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u6 (And.intro u10 (And.intro u4 (And.intro u3 (And.intro u11 (And.intro u1 (And.intro u0 (And.intro u9 (And.intro u12 (And.intro u2 (And.intro u8 u7)))))))))))))) h

theorem clause14400 (t x01 x12 x15 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
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
  have u3 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8733 t x01 x12 x15 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u6 (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u1 u4)))))))) h

theorem clause14401 (t x01 x15 x17 x25 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x15 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x57)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x15 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x25 + ((-1) * x57)) ≥ 1) := by
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
  have h := NineTheoryTrial.th8734 t x01 x15 x17 x25 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u5 (And.intro u3 (And.intro u2 u0))))))) h

theorem clause14402 (t x02 x03 x05 x12 x13 x25 x34 x47 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + x47 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x12 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + x47 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8735 t x02 x03 x05 x12 x13 x25 x34 x47 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u6 (And.intro u5 (And.intro u7 (And.intro u0 (And.intro u1 (And.intro u8 (And.intro u4 (And.intro u3 (And.intro u10 u9)))))))))))) h

theorem clause14403 (t x02 x04 x25 x34 x46 x47 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((t + x02 + ((-1) * x04)) ≥ 1)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ (x46 ≥ 0)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
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
  have u3 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x02 + ((-1) * x04)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x46 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8736 t x02 x04 x25 x34 x46 x47 x56 x67
  exact (fun hh => (fun hh => hh u9) (hh (And.intro u8 (And.intro u4 (And.intro u3 (And.intro u7 (And.intro u5 (And.intro u2 (And.intro u6 (And.intro u0 u1)))))))))) h

theorem clause14404 (t x01 x02 x05 x14 x25 x47 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + x47 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x47 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8737 t x01 x02 x05 x14 x25 x47 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u7 (And.intro u8 (And.intro u5 (And.intro u2 (And.intro u4 (And.intro u0 u6)))))))))) h

theorem clause14405 (t x03 x13 x14 x34 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((t + ((-1) * x03) + x13) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x03) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8740 t x03 x13 x14 x34 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u4 (And.intro u1 u5))))))) h

theorem clause14406 (t x01 x02 x05 x13 x25 x34 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1))) ∨ ((t + ((-1) * x57)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8742 t x01 x02 x05 x13 x25 x34 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u10 (And.intro u0 (And.intro u7 (And.intro u9 (And.intro u6 (And.intro u2 (And.intro u4 (And.intro u5 (And.intro u3 u1)))))))))))) h

theorem clause14407 (t x05 x24 x25 x45 x47 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + x45 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x05 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x45 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8743 t x05 x24 x25 x45 x47 x56
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u3 (And.intro u0 (And.intro u6 (And.intro u5 (And.intro u4 u2))))))) h

theorem clause14408 (t x04 x13 x23 x24 x34 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((t + x13 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x13 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8745 t x04 x13 x23 x24 x34 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u6 (And.intro u1 u4)))))))) h

theorem clause14409 (t x01 x02 x13 x25 x37 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + x37 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x37 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8746 t x01 x02 x13 x25 x37 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u3 (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u7 u6))))))))) h

theorem clause14410 (t x04 x13 x23 x24 x34 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((t + x13 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x13 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8747 t x04 x13 x23 x24 x34 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u5 (And.intro u6 (And.intro u3 (And.intro u2 u0)))))))) h

theorem clause14411 (t x01 x02 x16 x25 x46 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ (x46 ≥ 0)) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x46 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x16 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8748 t x01 x02 x16 x25 x46 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u9 (And.intro u8 (And.intro u1 (And.intro u6 (And.intro u3 (And.intro u5 (And.intro u4 (And.intro u2 u0))))))))))) h

theorem clause14412 (t x01 x02 x03 x13 x25 x34 x35 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ (x35 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x35 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8750 t x01 x02 x03 x13 x25 x34 x35 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u5 (And.intro u4 (And.intro u9 (And.intro u1 (And.intro u10 (And.intro u7 (And.intro u0 (And.intro u8 (And.intro u2 u3)))))))))))) h

theorem clause14413 (t x06 x13 x36 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x06 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8751 t x06 x13 x36 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u3 (And.intro u0 (And.intro u6 (And.intro u7 (And.intro u4 u2))))))))) h

theorem clause14414 (t x01 x02 x17 x25 x56 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th8752 t x01 x02 x17 x25 x56 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u7 (And.intro u3 (And.intro u0 (And.intro u6 (And.intro u4 (And.intro u2 u5))))))))) h

theorem clause14415 (t x02 x25 x56 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x02 ≥ 0)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
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
  have u4 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8754 t x02 x25 x56 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u6 (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u5 u4)))))))) h

theorem clause14416 (t x02 x25 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ (x02 ≥ 0)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8755 t x02 x25 x57 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u5 u6)))))))) h

theorem clause14417 (t x01 x14 x34 x46 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ (x46 ≥ 0)) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8756 t x01 x14 x34 x46 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u6 (And.intro u5 (And.intro u3 (And.intro u2 u1)))))))) h

theorem clause14418 (x04 x14 x34 : ℝ) : (((x14 + ((-1) * x34)) ≥ 0) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x34)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8757 x04 x14 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause14419 (x14 x34 x46 : ℝ) : ((¬ ((x14 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ ((x14 + ((-1) * x46)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x14 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x14 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8760 x14 x34 x46
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause14420 (x34 x46 x47 : ℝ) : (((x34 + ((-1) * x47)) ≥ 1) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x47)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8764 x34 x46 x47
  exact (fun hh => u0 (hh (And.intro u2 u1))) h

theorem clause14421 (t x01 x03 x15 x34 x46 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x57) + x67) ≥ 1) := by
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
  have h := NineTheoryTrial.th8766 t x01 x03 x15 x34 x46 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u2 (And.intro u4 (And.intro u7 (And.intro u3 (And.intro u0 (And.intro u5 u1))))))))) h

theorem clause14422 (t x02 x03 x12 x13 x25 x34 x46 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x12 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x57) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8769 t x02 x03 x12 x13 x25 x34 x46 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u9 (And.intro u6 (And.intro u8 u5))))))))))) h

theorem clause14424 (t x25 x35 x36 x56 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x25) + x35) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x25) + x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8771 t x25 x35 x36 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u5 (And.intro u0 u4))))))) h

theorem clause14425 (t x01 x02 x05 x12 x13 x16 x36 x56 x57 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((t + x67 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x57)) ≥ 0)) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x36)) ≥ 0))) := by
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
  have u3 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x67 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x56 + ((-1) * x57)) ≥ 0) := by
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
  have u10 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x16 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th8772 t x01 x02 x05 x12 x13 x16 x36 x56 x57 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u9 (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u6 (And.intro u5 (And.intro u4 (And.intro u11 (And.intro u7 (And.intro u10 u8))))))))))))) h

theorem clause14426 (x06 x46 x67 : ℝ) : ((¬ ((x06 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ ((x06 + ((-1) * x67)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x06 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x06 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8774 x06 x46 x67
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause14427 (t x03 x13 x17 x27 x34 x46 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + ((-1) * x27) + x67) ≥ 1)) ∨ (¬ ((t + ((-1) * x13) + x17) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x27) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x13) + x17) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8775 t x03 x13 x17 x27 x34 x46 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u7 (And.intro u6 (And.intro u0 (And.intro u8 (And.intro u3 (And.intro u4 u5)))))))))) h

theorem clause14428 (t x03 x12 x13 x27 x34 x46 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((t + x68 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x12 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x68 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x27 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8776 t x03 x12 x13 x27 x34 x46 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u7 (And.intro u0 (And.intro u2 (And.intro u3 (And.intro u8 (And.intro u6 u4)))))))))) h

theorem clause14429 (t x35 x56 x57 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + x67 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x67)) ≥ 0)) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x67 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8777 t x35 x56 x57 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u0 u3))))))) h

theorem clause14431 (x04 x46 x47 : ℝ) : (((x04 + ((-1) * x47)) ≥ 1) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x47)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8780 x04 x46 x47
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause14433 (t x01 x03 x12 x24 x34 x45 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ (x67 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8782 t x01 x03 x12 x24 x34 x45 x46 x67
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u2 (And.intro u3 (And.intro u5 (And.intro u9 (And.intro u1 (And.intro u7 (And.intro u6 (And.intro u0 u8)))))))))) h

theorem clause14434 (x03 x13 x34 x36 : ℝ) : ((¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th8784 x03 x13 x34 x36
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause14435 (t x03 x34 x46 x47 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ ((t + ((-1) * x03)) ≤ 0) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x47)) ≥ 0)) ∨ (¬ (x67 ≥ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x03)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8786 t x03 x34 x46 x47 x67 x78
  exact (fun hh => (fun hh => hh u7) (hh (And.intro u5 (And.intro u6 (And.intro u0 (And.intro u2 (And.intro u1 (And.intro u4 u3)))))))) h

theorem clause14436 (t x01 x02 x14 x25 x46 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
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
  have u6 : ((t + ((-1) * x57) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8789 t x01 x02 x14 x25 x46 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u5 (And.intro u6 (And.intro u7 (And.intro u2 (And.intro u1 u3))))))))) h

theorem clause14437 (t x02 x25 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ (x02 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8790 t x02 x25 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u6 (And.intro u2 (And.intro u1 u5)))))))) h

theorem clause14439 (t x02 x03 x25 x36 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((t + x02 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x46 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x02 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x46 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8795 t x02 x03 x25 x36 x46 x56 x67
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u7 (And.intro u2 (And.intro u4 (And.intro u1 (And.intro u5 (And.intro u6 u0)))))))) h

theorem clause14440 (t x02 x03 x25 x34 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((t + x02 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
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
  have u3 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x02 + ((-1) * x03)) ≥ 1) := by
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
  have u7 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8796 t x02 x03 x25 x34 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u5 (And.intro u2 u6))))))))) h

theorem clause14442 (t x01 x02 x13 x26 x36 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + x36 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x36 + ((-1) * x56)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8799 t x01 x02 x13 x26 x36 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u7 (And.intro u4 (And.intro u6 (And.intro u0 (And.intro u5 u2))))))))) h

theorem clause14443 (t x03 x06 x13 x14 x34 x36 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x14 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((t + ((-1) * x03) + x13) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + x46 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x03) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x46 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8800 t x03 x06 x13 x14 x34 x36 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u4 (And.intro u6 (And.intro u8 (And.intro u5 (And.intro u9 (And.intro u0 (And.intro u3 (And.intro u1 u7))))))))))) h

theorem clause14444 (t x02 x24 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ (x02 ≥ 0)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8801 t x02 x24 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u4 (And.intro u3 (And.intro u1 u6)))))))) h

theorem clause14445 (t x01 x13 x15 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x13)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8802 t x01 x13 x15 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u5 (And.intro u0 (And.intro u4 (And.intro u2 u6)))))))) h

theorem clause14446 (t x03 x23 x34 x35 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + ((-1) * x45) + x46) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x45) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8804 t x03 x23 x34 x35 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u2 (And.intro u6 (And.intro u0 (And.intro u3 u1)))))))) h

theorem clause14447 (t x06 x24 x26 x34 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x24) + x34) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1))) := by
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
  have u3 : ((x06 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8808 t x06 x24 x26 x34 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u6 (And.intro u4 (And.intro u0 (And.intro u2 (And.intro u1 u5)))))))) h

theorem clause14448 (t x04 x06 x23 x26 x34 x35 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x34 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x26)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x34 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x23 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8809 t x04 x06 x23 x26 x34 x35 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u5 (And.intro u2 (And.intro u6 (And.intro u0 u7))))))))) h

theorem clause14449 (x05 x56 x57 : ℝ) : ((¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x57)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1)))) := by
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
  have u2 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8810 x05 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 u2)))) h

theorem clause14451 (t x03 x23 x26 x36 x67 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + x03 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x26)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + x03 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8812 t x03 x23 x26 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u4 u1))))))) h

theorem clause14452 (t x02 x05 x12 x14 x24 x25 x35 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((t + x02 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((t + x35 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x02 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x35 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x14 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8813 t x02 x05 x12 x14 x24 x25 x35 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u6 (And.intro u1 (And.intro u3 (And.intro u8 (And.intro u9 (And.intro u5 (And.intro u7 u2))))))))))) h

theorem clause14453 (t x01 x06 x13 x26 x35 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x06) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + ((-1) * x26) + x56) ≥ 1))) := by
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
  have u3 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x01) + x06) ≥ 1) := by
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
  have h := NineTheoryTrial.th8814 t x01 x06 x13 x26 x35 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u7 (And.intro u2 (And.intro u3 (And.intro u6 (And.intro u4 u5))))))))) h

theorem clause14454 (t x03 x13 x15 x35 x56 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x03) + x13) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x15)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x03) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8815 t x03 x13 x15 x35 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u1 u5))))))) h

theorem clause14455 (t x05 x13 x15 x23 x35 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + x13 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x15)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
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
  have u4 : ((x05 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8816 t x05 x13 x15 x23 x35 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u6 (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u1 u4)))))))) h

theorem clause14456 (t x05 x35 x56 : ℝ) : ((¬ (x56 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x05) + x35) ≥ 1) ∨ ((t + ((-1) * x05)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x05) + x35) ≥ 1) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x05)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th8817 t x05 x35 x56
  exact (fun hh => u2 (hh (And.intro u1 (And.intro u3 u0)))) h

theorem clause14457 (t x02 x25 x35 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8820 t x02 x25 x35 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u1 u6)))))))) h

theorem clause14458 (x25 x35 x56 : ℝ) : ((¬ ((x25 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x25 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8821 x25 x35 x56
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u0 u1))) h

theorem clause14460 (t x02 x12 x24 x25 x34 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ (x46 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x46 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8825 t x02 x12 x24 x25 x34 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u6 (And.intro u7 (And.intro u5 (And.intro u2 (And.intro u1 (And.intro u4 u3))))))))) h

theorem clause14461 (t x04 x12 x24 x25 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x25)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ (x04 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x25)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8826 t x04 x12 x24 x25 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u5 (And.intro u3 u6)))))))) h

theorem clause14462 (t x02 x04 x12 x14 x23 x27 x34 x46 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x14 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ (x34 ≥ 0)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((t + x27 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x12 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((t + x27 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8827 t x02 x04 x12 x14 x23 x27 x34 x46 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u0 (And.intro u3 (And.intro u7 (And.intro u1 (And.intro u10 (And.intro u6 (And.intro u9 (And.intro u8 u2)))))))))))) h

theorem clause14463 (t x12 x24 x27 x47 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x24 ≥ 0)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x47)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x24 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x27 + ((-1) * x47)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8828 t x12 x24 x27 x47 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u6 (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u7 (And.intro u5 u4))))))))) h

theorem clause14464 (t x01 x02 x12 x23 x24 x27 x37 x47 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ (¬ (x24 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + x37 + ((-1) * x67)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x27 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x02)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x24 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x37 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x27 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x12 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th8829 t x01 x02 x12 x23 x24 x27 x37 x47 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u10 (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u5 (And.intro u9 (And.intro u6 (And.intro u11 (And.intro u7 u1))))))))))))) h

theorem clause14465 (t x03 x05 x12 x13 x24 x35 x46 x56 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x12 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x03 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th8830 t x03 x05 x12 x13 x24 x35 x46 x56 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u9 (And.intro u8 (And.intro u10 (And.intro u11 (And.intro u5 (And.intro u0 (And.intro u3 (And.intro u4 (And.intro u6 u7))))))))))))) h

theorem clause14466 (t x02 x03 x04 x13 x23 x35 x37 x47 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x04)) ≤ 0)) ∨ (¬ (x02 ≥ 0)) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((t + x37 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((t + x37 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th8831 t x02 x03 x04 x13 x23 x35 x37 x47 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u4 (And.intro u2 (And.intro u11 (And.intro u10 (And.intro u9 (And.intro u8 (And.intro u6 u5))))))))))))) h

theorem clause14467 (x25 x35 x56 : ℝ) : ((¬ ((x25 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ ((x25 + ((-1) * x56)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x25 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x25 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8832 x25 x35 x56
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause14468 (t x12 x13 x23 x24 x35 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((t + ((-1) * x23) + x24) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x23) + x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8833 t x12 x13 x23 x24 x35
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u4 (And.intro u1 (And.intro u3 (And.intro u0 u2)))))) h

theorem clause14469 (t x01 x12 x13 x23 x35 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ (x12 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8834 t x01 x12 x13 x23 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u4 (And.intro u3 (And.intro u6 (And.intro u1 u2)))))))) h

theorem clause14470 (t x01 x03 x04 x13 x24 x34 x35 x46 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + ((-1) * x24) + x34) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x04) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x24) + x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x01) + x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8835 t x01 x03 x04 x13 x24 x34 x35 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u8 (And.intro u3 (And.intro u1 (And.intro u6 (And.intro u4 (And.intro u5 (And.intro u2 u0)))))))))) h

theorem clause14471 (t x03 x04 x13 x15 x34 x35 x46 x57 x67 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x03) + x13) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x03) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x15 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x15 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8836 t x03 x04 x13 x15 x34 x35 x46 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u8 (And.intro u6 (And.intro u0 (And.intro u9 (And.intro u5 (And.intro u4 u7))))))))))) h

theorem clause14472 (t x03 x04 x06 x13 x15 x34 x35 x46 x56 x67 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x03) + x13) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x03) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x46) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x15 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8837 t x03 x04 x06 x13 x15 x34 x35 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u9 (And.intro u0 (And.intro u6 (And.intro u7 (And.intro u10 (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u2 (And.intro u5 u8)))))))))))) h

theorem clause14473 (t x01 x02 x03 x13 x24 x34 x35 x46 x67 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x34 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8839 t x01 x02 x03 x13 x24 x34 x35 x46 x67
  exact (fun hh => (fun hh => hh u7) (hh (And.intro u5 (And.intro u6 (And.intro u10 (And.intro u0 (And.intro u4 (And.intro u9 (And.intro u8 (And.intro u3 (And.intro u2 u1))))))))))) h

theorem clause14474 (t x01 x03 x13 x35 x37 x78 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ (x78 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8843 t x01 x03 x13 x35 x37 x78
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u3 (And.intro u5 (And.intro u6 u7)))))))) h

theorem clause14477 (t x01 x03 x15 x35 x56 x57 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ ((t + ((-1) * x01)) ≤ 0)) := by
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
  have u3 : ((x01 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8846 t x01 x03 x15 x35 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u3 (And.intro u4 (And.intro u0 (And.intro u6 (And.intro u5 u7))))))))) h

theorem clause14478 (t x01 x04 x15 x17 x46 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x04) ≥ 1)) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x17)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x01) + x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x15 + ((-1) * x17)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8847 t x01 x04 x15 x17 x46 x57 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u6 (And.intro u5 (And.intro u7 u8)))))))))) h

theorem clause14479 (t x01 x02 x03 x04 x13 x24 x34 x37 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + ((-1) * x24) + x34) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x24) + x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x03 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x13 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8849 t x01 x02 x03 x04 x13 x24 x34 x37 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u9 (And.intro u5 (And.intro u0 (And.intro u1 (And.intro u6 (And.intro u7 (And.intro u4 (And.intro u8 (And.intro u3 u2))))))))))) h

theorem clause14480 (t x02 x12 x24 x26 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
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
  have h := NineTheoryTrial.th8850 t x02 x12 x24 x26 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u6 u5)))))))) h

theorem clause14481 (t x02 x04 x12 x24 x25 x26 x46 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ ((t + ((-1) * x25)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x26 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((t + ((-1) * x67) + x68) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x25)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x26 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((t + ((-1) * x67) + x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8852 t x02 x04 x12 x24 x25 x26 x46 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u8 (And.intro u0 (And.intro u3 (And.intro u6 (And.intro u10 (And.intro u4 (And.intro u9 (And.intro u1 (And.intro u7 u5)))))))))))) h

theorem clause14482 (t x06 x13 x34 x36 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ ((t + ((-1) * x46)) ≤ 0) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x36)) ≥ 0)) ∨ (¬ (x34 ≥ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8854 t x06 x13 x34 x36 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u6 (And.intro u4 (And.intro u5 (And.intro u1 (And.intro u2 u7))))))))) h

theorem clause14483 (t x01 x03 x06 x13 x35 x36 x46 x67 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + x36 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x06) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x36 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x01) + x06) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8856 t x01 x03 x06 x13 x35 x36 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u5 (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u7 (And.intro u6 u4)))))))))) h

theorem clause14484 (t x03 x04 x12 x13 x24 x35 x37 x46 x67 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ ((t + ((-1) * x03)) ≤ 0) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((t + x37 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x03)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((t + x37 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8857 t x03 x04 x12 x13 x24 x35 x37 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u9 (And.intro u7 (And.intro u1 (And.intro u4 (And.intro u10 (And.intro u2 (And.intro u6 (And.intro u8 u5)))))))))))) h

theorem clause14485 (t x13 x34 x37 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ (x34 ≥ 0)) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8858 t x13 x34 x37 x67 x78
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u5 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u2 u6))))))) h

theorem clause14486 (t x04 x12 x24 x46 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ (x12 ≥ 0)) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
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
  have u3 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th8859 t x04 x12 x24 x46 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u5 (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u6 u7))))))))) h

theorem clause14487 (t x01 x04 x15 x24 x46 x47 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x47) + x57) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x04) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x47) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x01) + x04) ≥ 1) := by
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
  have h := NineTheoryTrial.th8861 t x01 x04 x15 x24 x46 x47 x57
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u5 (And.intro u3 (And.intro u7 (And.intro u6 (And.intro u2 (And.intro u4 u0)))))))) h

theorem clause14488 (t x03 x13 x23 x34 x35 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8862 t x03 x13 x23 x34 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u0 (And.intro u6 (And.intro u2 (And.intro u3 u1)))))))) h

theorem clause14489 (t x01 x02 x03 x15 x36 x46 x56 x67 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x46) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th8863 t x01 x02 x03 x15 x36 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u6 (And.intro u4 (And.intro u3 u8)))))))))) h

theorem clause14490 (t x03 x23 x35 x37 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8865 t x03 x23 x35 x37 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u4 u6)))))))) h

theorem clause14491 (t x01 x04 x13 x24 x36 x46 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((t + x36 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x04) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x36 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x01) + x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8867 t x01 x04 x13 x24 x36 x46 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u6 (And.intro u4 (And.intro u5 u7))))))))) h

theorem clause14492 (t x01 x02 x15 x24 x47 x58 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + x58 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x58)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x58 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x15 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8868 t x01 x02 x15 x24 x47 x58 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u7 (And.intro u6 (And.intro u1 (And.intro u0 (And.intro u3 u4))))))))) h

theorem clause14493 (t x05 x15 x23 x35 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x05 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x56)) ≥ 1) := by
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
  have h := NineTheoryTrial.th8870 t x05 x15 x23 x35 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u7 (And.intro u6 (And.intro u5 (And.intro u0 (And.intro u2 (And.intro u4 u1))))))))) h

theorem clause14494 (t x01 x02 x15 x24 x46 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
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
  have u3 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th8871 t x01 x02 x15 x24 x46 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u6 (And.intro u7 (And.intro u4 u2))))))))) h

theorem clause14495 (t x03 x13 x24 x34 x36 x46 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + ((-1) * x24) + x34) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x46)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x24) + x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8872 t x03 x13 x24 x34 x36 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u6 (And.intro u4 (And.intro u0 (And.intro u2 u5)))))))) h

theorem clause14496 (t x03 x24 x36 x37 x45 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x36 ≥ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x47)) ≤ 0)) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x36 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 + ((-1) * x47)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8873 t x03 x24 x36 x37 x45 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u5 (And.intro u0 (And.intro u6 (And.intro u2 (And.intro u7 u4))))))))) h

theorem clause14498 (t x03 x13 x23 x34 x35 x37 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ (x34 ≥ 0)) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x13 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8875 t x03 x13 x23 x34 x35 x37
  exact (fun hh => (fun hh => hh u7) (hh (And.intro u2 (And.intro u5 (And.intro u1 (And.intro u6 (And.intro u0 (And.intro u4 u3)))))))) h

theorem clause14499 (x37 x57 x78 : ℝ) : ((¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x57)) ≥ 0)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x37 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8876 x37 x57 x78
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u1 u2))) h

theorem clause14500 (t x01 x04 x15 x46 x58 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x04) ≥ 1)) ∨ (¬ ((t + x58 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x58)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x01) + x04) ≥ 1) := by
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
  have h := NineTheoryTrial.th8877 t x01 x04 x15 x46 x58 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u7 (And.intro u2 (And.intro u1 (And.intro u3 (And.intro u6 (And.intro u5 u4))))))))) h

theorem clause14501 (t x01 x02 x06 x12 x13 x15 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
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
  have u3 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x46) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8879 t x01 x02 x06 x12 x13 x15 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u4 (And.intro u5 (And.intro u6 (And.intro u9 (And.intro u8 (And.intro u2 (And.intro u7 u3))))))))))) h

theorem clause14502 (t x01 x06 x13 x35 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x06) ≥ 1))) := by
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
  have u3 : ((t + ((-1) * x46) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x01) + x06) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8880 t x01 x06 x13 x35 x46 x56 x67
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u6 (And.intro u5 (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u7 u4)))))))) h

theorem clause14503 (t x01 x05 x12 x15 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x58)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x58)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x12 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8883 t x01 x05 x12 x15 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u0 (And.intro u5 (And.intro u4 u2))))))) h

theorem clause14504 (t x02 x03 x04 x12 x13 x24 x35 x46 x47 x56 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + x12 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x46) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8884 t x02 x03 x04 x12 x13 x24 x35 x46 x47 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u9 (And.intro u0 (And.intro u3 (And.intro u5 (And.intro u7 (And.intro u8 (And.intro u2 (And.intro u1 (And.intro u10 u4)))))))))))) h

theorem clause14505 (t x16 x46 x56 : ℝ) : ((¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ ((t + x16 + ((-1) * x46)) ≥ 1) ∨ (¬ ((x16 + ((-1) * x56)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x46) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + x16 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x16 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8885 t x16 x46 x56
  exact (fun hh => u1 (hh (And.intro u0 u2))) h

theorem clause14506 (t x01 x02 x04 x12 x13 x17 x24 x37 x47 x48 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ (x78 ≥ 0)) ∨ ((t + ((-1) * x47)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x48)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x48)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x12 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x17 + ((-1) * x37)) ≥ 0) := by
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
  have u10 : ¬ ((t + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x04 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))))
  have u12 : ((x24 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))))
  have h := NineTheoryTrial.th8886 t x01 x02 x04 x12 x13 x17 x24 x37 x47 x48 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u10 (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u4 (And.intro u7 (And.intro u6 (And.intro u8 (And.intro u9 (And.intro u11 (And.intro u5 u12)))))))))))))) h

theorem clause14507 (t x01 x02 x12 x13 x17 x24 x37 x48 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + ((-1) * x48) + x78) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x48)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x12 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x48) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x24 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8887 t x01 x02 x12 x13 x17 x24 x37 x48 x78
  exact (fun hh => (fun hh => hh u9) (hh (And.intro u6 (And.intro u3 (And.intro u4 (And.intro u7 (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u5 u8)))))))))) h

theorem clause14508 (t x01 x06 x12 x13 x35 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x06)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x12 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x46) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8889 t x01 x06 x12 x13 x35 x46 x56 x67
  exact (fun hh => (fun hh => hh u8) (hh (And.intro u1 (And.intro u7 (And.intro u2 (And.intro u6 (And.intro u4 (And.intro u0 (And.intro u5 u3))))))))) h

theorem clause14509 (t x36 x37 x46 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x36 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x37)) ≤ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x36 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x37)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8890 t x36 x37 x46 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u4 (And.intro u5 u2))))))) h

theorem clause14511 (x04 x14 x46 : ℝ) : ((¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ ((x14 + ((-1) * x46)) ≤ (-1)) ∨ (¬ ((x04 + ((-1) * x14)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8892 x04 x14 x46
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause14512 (t x02 x05 x26 x35 x56 x58 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x02 + ((-1) * x05)) ≥ 1)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x05 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x02 + ((-1) * x05)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x05 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x56)) ≥ 1) := by
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
  have u7 : ((x35 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8893 t x02 x05 x26 x35 x56 x58 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u6 (And.intro u4 (And.intro u9 (And.intro u8 (And.intro u3 (And.intro u7 u1))))))))))) h

theorem clause14513 (t x04 x24 x26 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((t + x04 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1))) := by
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
  have u3 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8894 t x04 x24 x26 x46 x67
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u2 (And.intro u4 (And.intro u1 (And.intro u3 u0)))))) h

theorem clause14514 (x05 x15 x58 : ℝ) : ((¬ ((x05 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x15)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x05 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x15 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8897 x05 x15 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 u0)))) h

theorem clause14515 (t x02 x04 x05 x24 x35 x46 x47 x57 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + x02 + ((-1) * x05)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x35 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ ((t + ((-1) * x47)) ≤ 0) ∨ (¬ (x58 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x02 + ((-1) * x05)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ¬ ((t + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : (x58 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8898 t x02 x04 x05 x24 x35 x46 x47 x57 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u9 (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u5 (And.intro u10 (And.intro u6 (And.intro u7 (And.intro u4 u8)))))))))))) h

theorem clause14516 (t x03 x04 x13 x14 x24 x35 x46 x47 x57 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + ((-1) * x47) + x57) ≥ 1)) ∨ (¬ ((t + ((-1) * x13) + x14) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x14)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x47) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x13) + x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x04 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8899 t x03 x04 x13 x14 x24 x35 x46 x47 x57
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u6 (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u2 (And.intro u8 (And.intro u7 (And.intro u9 u0)))))))))) h

theorem clause14517 (t x02 x04 x05 x24 x35 x46 x47 x56 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + x02 + ((-1) * x05)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x04)) ≤ 0)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x05 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1))) ∨ ((t + ((-1) * x47)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x02 + ((-1) * x05)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x05 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x35 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ¬ ((t + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8900 t x02 x04 x05 x24 x35 x46 x47 x56 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u10 (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u5 (And.intro u9 (And.intro u8 (And.intro u7 (And.intro u6 u4)))))))))))) h

theorem clause14518 (t x01 x14 x17 x24 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x17 + ((-1) * x47)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((t + x14 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x17 + ((-1) * x47)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x14 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8901 t x01 x14 x17 x24 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u4 (And.intro u5 (And.intro u0 u3))))))) h

theorem clause14519 (t x04 x06 x24 x46 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + x04 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x68)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x04 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8903 t x04 x06 x24 x46 x68
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u4 (And.intro u1 (And.intro u0 (And.intro u3 u2)))))) h

theorem clause14520 (t x01 x04 x12 x13 x14 x17 x47 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + x17 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
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
  have u3 : ((x04 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x17 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8906 t x01 x04 x12 x13 x14 x17 x47 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u9 (And.intro u3 (And.intro u1 (And.intro u7 (And.intro u6 (And.intro u8 (And.intro u0 (And.intro u4 (And.intro u2 u5))))))))))) h

theorem clause14521 (t x02 x03 x26 x35 x58 x67 x78 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + x02 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((t + x58 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + x02 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x58 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x58)) ≥ 1) := by
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
  have u7 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8907 t x02 x03 x26 x35 x58 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u7 (And.intro u5 (And.intro u6 (And.intro u3 (And.intro u2 (And.intro u4 u0))))))))) h

theorem clause14522 (t x01 x04 x12 x13 x14 x15 x24 x35 x45 x46 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x04 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x14)) ≤ 0)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x15 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
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
  have u3 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x04 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x12 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x15 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))))
  have u12 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))))
  have h := NineTheoryTrial.th8911 t x01 x04 x12 x13 x14 x15 x24 x35 x45 x46 x56
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u7 (And.intro u9 (And.intro u2 (And.intro u12 (And.intro u8 (And.intro u6 (And.intro u11 (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u10 u3))))))))))))) h

theorem clause14523 (t x02 x12 x24 x26 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8912 t x02 x12 x24 x26 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u7 (And.intro u3 (And.intro u2 u4))))))))) h

theorem clause14524 (t x02 x05 x23 x35 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x05)) ≥ 0)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x05)) ≥ 0) := by
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
  have u6 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8914 t x02 x05 x23 x35 x56 x57
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u1 (And.intro u6 (And.intro u5 (And.intro u7 (And.intro u0 (And.intro u4 u2)))))))) h

theorem clause14525 (t x03 x05 x12 x15 x23 x24 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x23) + x24) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x15)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x23) + x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x24)) ≥ 1) := by
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
  have h := NineTheoryTrial.th8915 t x03 x05 x12 x15 x23 x24 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u5 (And.intro u7 u6))))))))) h

theorem clause14526 (t x01 x15 x35 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8916 t x01 x15 x35 x56 x57
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u1 (And.intro u6 (And.intro u5 (And.intro u3 (And.intro u0 u2))))))) h

theorem clause14527 (t x35 x56 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x56)) ≥ 1) := by
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
  have u6 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8917 t x35 x56 x57 x67 x78
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u6 (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u5 u3))))))) h

theorem clause14528 (t x01 x04 x13 x35 x46 x56 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((t + ((-1) * x01) + x04) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
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
  have u3 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x01) + x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8918 t x01 x04 x13 x35 x46 x56 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u7 (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u3 (And.intro u4 (And.intro u8 (And.intro u6 u9))))))))))) h

theorem clause14529 (t x35 x37 x56 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x37)) ≤ 0)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x56)) ≥ 1) := by
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
  have u4 : ((x35 + ((-1) * x37)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8919 t x35 x37 x56 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u3 (And.intro u1 u5))))))) h

theorem clause14530 (t x04 x06 x12 x24 x46 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x68)) ≤ (-1))) ∨ (¬ (x12 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x06 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8921 t x04 x06 x12 x24 x46 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u6 (And.intro u5 (And.intro u0 (And.intro u7 (And.intro u1 (And.intro u4 (And.intro u2 u3)))))))))) h

theorem clause14531 (t x03 x12 x13 x24 x35 x46 x57 x67 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1))) := by
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
  have u3 : ((t + x12 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8922 t x03 x12 x13 x24 x35 x46 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u7 (And.intro u3 (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u8 (And.intro u6 u2)))))))))) h

theorem clause14533 (t x01 x02 x06 x12 x13 x14 x26 x34 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x14 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((t + ((-1) * x26) + x46) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x06)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x12 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x26) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x02 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8924 t x01 x02 x06 x12 x13 x14 x26 x34 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u5 (And.intro u10 (And.intro u0 (And.intro u6 (And.intro u9 (And.intro u8 (And.intro u1 (And.intro u7 u3)))))))))))) h

theorem clause14534 (t x01 x02 x12 x13 x15 x26 x35 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x12 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x12)) ≥ 0) := by
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
  have u8 : ((x15 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8925 t x01 x02 x12 x13 x15 x26 x35 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u9 (And.intro u1 (And.intro u5 (And.intro u7 (And.intro u3 (And.intro u6 (And.intro u0 u8))))))))))) h

theorem clause14535 (t x13 x35 x36 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1)))) := by
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
  have u3 : ((x36 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x56 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8931 t x13 x35 x36 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u5 (And.intro u1 u3))))))) h

theorem clause14536 (x13 x34 x37 : ℝ) : (((x13 + ((-1) * x34)) ≥ 1) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x37)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x37)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8933 x13 x34 x37
  exact (fun hh => u0 (hh (And.intro u2 u1))) h

theorem clause14537 (t x04 x45 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ ((t + ((-1) * x45)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x56 ≥ 0) := by
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
  have u6 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8938 t x04 x45 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u5 (And.intro u0 (And.intro u4 (And.intro u6 u2)))))))) h

theorem clause14538 (t x01 x02 x13 x26 x37 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x68) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8939 t x01 x02 x13 x26 x37 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u3 (And.intro u7 (And.intro u2 (And.intro u1 (And.intro u5 (And.intro u4 u0))))))))) h

theorem clause14539 (t x01 x02 x12 x13 x26 x27 x35 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((t + ((-1) * x27) + x57) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
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
  have u4 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x27) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x02 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8943 t x01 x02 x12 x13 x26 x27 x35 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u7 (And.intro u0 (And.intro u2 (And.intro u1 (And.intro u5 (And.intro u9 (And.intro u8 (And.intro u4 u6))))))))))) h

theorem clause14540 (t x27 x57 x67 : ℝ) : ((¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x67)) ≤ 0)) ∨ ((t + ((-1) * x27) + x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x27 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x27) + x57) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8944 t x27 x57 x67
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause14541 (t x02 x24 x25 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((t + ((-1) * x45) + x46) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x25 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x45) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8945 t x02 x24 x25 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u2 u5))))))) h

theorem clause14542 (t x12 x13 x23 x26 x35 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x23) + x26) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th8946 t x12 x13 x23 x26 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u0 (And.intro u1 (And.intro u3 u4))))))) h

theorem clause14543 (t x02 x03 x23 x26 x35 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((t + ((-1) * x23) + x26) ≥ 1))) := by
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
  have u4 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x23) + x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8947 t x02 x03 x23 x26 x35
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u1 (And.intro u0 (And.intro u5 (And.intro u2 u4)))))) h

theorem clause14544 (t x02 x04 x12 x24 x26 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x24)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8949 t x02 x04 x12 x24 x26 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u5 (And.intro u6 (And.intro u7 (And.intro u3 (And.intro u4 u2))))))))) h

theorem clause14545 (t x01 x02 x12 x14 x26 x27 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + ((-1) * x27) + x57) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x27) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x02 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8950 t x01 x02 x12 x14 x26 x27 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u7 (And.intro u4 (And.intro u0 (And.intro u2 (And.intro u3 (And.intro u1 (And.intro u9 (And.intro u6 u5))))))))))) h

theorem clause14548 (t x02 x05 x23 x25 x34 x35 x46 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x35)) ≤ 0)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x25 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ (x46 ≥ 0)) ∨ (¬ ((x05 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x25 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x46 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x05 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x25 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8953 t x02 x05 x23 x25 x34 x35 x46 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u6 (And.intro u0 (And.intro u9 (And.intro u7 (And.intro u2 (And.intro u4 (And.intro u1 (And.intro u3 u5))))))))))) h

theorem clause14549 (x24 x34 x46 : ℝ) : (((x24 + ((-1) * x46)) ≥ 1) ∨ (¬ ((x24 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8954 x24 x34 x46
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause14550 (t x02 x23 x27 x37 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x37 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x37 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8955 t x02 x23 x27 x37 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u5 (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u0 u4)))))))) h

theorem clause14551 (t x02 x07 x23 x25 x34 x37 x46 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ (x46 ≥ 0)) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x37)) ≤ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x46 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x07 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x34 + ((-1) * x37)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th8956 t x02 x07 x23 x25 x34 x37 x46 x57 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u7 (And.intro u2 (And.intro u5 (And.intro u6 (And.intro u8 (And.intro u4 (And.intro u9 (And.intro u10 u11))))))))))))) h

theorem clause14552 (t x01 x14 x34 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ (x46 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x46)) ≥ 1) := by
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
  have h := NineTheoryTrial.th8957 t x01 x14 x34 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u3 (And.intro u1 u4)))))))) h

theorem clause14554 (t x01 x06 x12 x13 x26 x35 x58 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x58 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x58)) ≥ 1)) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x06 + ((-1) * x26)) ≥ 0)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
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
  have u3 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x58 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x06 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8961 t x01 x06 x12 x13 x26 x35 x58 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u8 (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u9 (And.intro u6 (And.intro u3 (And.intro u7 (And.intro u10 u4)))))))))))) h

theorem clause14555 (t x02 x24 x27 x34 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x24) + x34) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x47)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x24) + x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8963 t x02 x24 x27 x34 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u2 (And.intro u1 (And.intro u5 u3))))))) h

theorem clause14556 (t x13 x23 x34 x35 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ (x46 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8964 t x13 x23 x34 x35 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u5 u6)))))))) h

theorem clause14557 (t x03 x13 x15 x35 x36 x37 x57 x67 x78 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x03) + x13) ≥ 1)) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x36 + ((-1) * x37)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x03) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x37)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8965 t x03 x13 x15 x35 x36 x37 x57 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u4 (And.intro u7 (And.intro u5 (And.intro u8 (And.intro u9 (And.intro u3 u6))))))))))) h

theorem clause14558 (t x04 x13 x23 x24 x34 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((t + x13 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x13 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8966 t x04 x13 x23 x24 x34 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u6 (And.intro u1 (And.intro u5 (And.intro u3 u2)))))))) h

theorem clause14559 (t x13 x23 x24 x34 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((t + x13 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x24)) ≥ 0))) := by
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
  have u3 : ((t + x13 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8967 t x13 x23 x24 x34 x46
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u3 (And.intro u5 (And.intro u0 (And.intro u4 u2)))))) h

theorem clause14561 (t x01 x02 x03 x13 x24 x34 x36 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((t + ((-1) * x45) + x46) ≥ 1))) := by
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
  have u3 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x36 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x45) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8969 t x01 x02 x03 x13 x24 x34 x36 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u7 (And.intro u2 (And.intro u9 (And.intro u5 (And.intro u8 (And.intro u3 u6))))))))))) h

theorem clause14563 (t x01 x02 x15 x26 x57 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x68)) ≤ (-1)) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x68) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8971 t x01 x02 x15 x26 x57 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u4 (And.intro u7 (And.intro u6 (And.intro u0 (And.intro u3 (And.intro u1 u5))))))))) h

theorem clause14564 (t x03 x06 x13 x26 x36 x37 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x03) + x13) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x26)) ≤ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x03) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x03 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8972 t x03 x06 x13 x26 x36 x37 x57 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u9 (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u3 (And.intro u8 (And.intro u6 u7))))))))))) h

theorem clause14565 (t x05 x13 x23 x25 x35 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x13 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x13 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8973 t x05 x13 x23 x25 x35 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u3 (And.intro u4 (And.intro u0 (And.intro u5 u6)))))))) h

theorem clause14566 (t x01 x02 x03 x13 x26 x34 x35 x67 x78 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ (x34 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x34 ≥ 0) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8974 t x01 x02 x03 x13 x26 x34 x35 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u3 (And.intro u7 (And.intro u8 (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u9 u10)))))))))))) h

theorem clause14567 (t x04 x16 x24 x45 x46 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x16 + ((-1) * x68)) ≤ (-1))) ∨ (¬ (x16 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x16 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8978 t x04 x16 x24 x45 x46 x68
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u5 (And.intro u6 (And.intro u2 u7)))))))) h

theorem clause14568 (t x01 x02 x03 x13 x16 x26 x35 x67 x68 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x16)) ≥ 0)) ∨ (¬ ((t + ((-1) * x67) + x68) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x01) + x02) ≥ 1) := by
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
  have u5 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x13 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x67) + x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x16 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th8981 t x01 x02 x03 x13 x16 x26 x35 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u7 (And.intro u1 (And.intro u6 (And.intro u8 (And.intro u2 (And.intro u5 (And.intro u0 (And.intro u9 u3))))))))))) h

theorem clause14569 (t x01 x02 x15 x17 x26 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x17)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x15 + ((-1) * x17)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th8982 t x01 x02 x15 x17 x26 x57 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u4 (And.intro u0 (And.intro u1 (And.intro u6 (And.intro u2 (And.intro u8 u7)))))))))) h

theorem clause14570 (x04 x24 x46 : ℝ) : (((x24 + ((-1) * x46)) ≥ 1) ∨ (¬ ((x04 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th8983 x04 x24 x46
  exact (fun hh => u0 (hh (And.intro u2 u1))) h

theorem clause14571 (t x01 x03 x04 x13 x14 x35 x37 x46 x47 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((t + x37 + ((-1) * x47)) ≥ 1)) ∨ (¬ (x14 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + x37 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : (x14 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8984 t x01 x03 x04 x13 x14 x35 x37 x46 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u10 (And.intro u2 (And.intro u5 (And.intro u4 (And.intro u8 (And.intro u1 (And.intro u9 (And.intro u7 (And.intro u0 u6)))))))))))) h

theorem clause14572 (t x13 x36 x37 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x36 ≥ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x36 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8985 t x13 x36 x37 x67 x78
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u6 (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u3 u0))))))) h

theorem clause14573 (t x01 x02 x13 x26 x35 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1)))) := by
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
  have u4 : ((t + ((-1) * x01) + x02) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8986 t x01 x02 x13 x26 x35 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u6 (And.intro u3 (And.intro u7 (And.intro u0 (And.intro u2 u1))))))))) h

theorem clause14574 (t x01 x02 x13 x26 x36 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + x36 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x36 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x67)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th8987 t x01 x02 x13 x26 x36 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u5 (And.intro u2 u6))))))))) h

theorem clause14575 (t x03 x05 x13 x35 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + ((-1) * x03) + x13) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x05)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x03) + x13) ≥ 1) := by
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
  have u5 : ((x03 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th8990 t x03 x05 x13 x35 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u3 (And.intro u5 (And.intro u2 u0))))))) h

theorem clause14577 (t x05 x07 x25 x35 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x07)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((t + ((-1) * x25) + x35) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x07)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x07 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x25) + x35) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8993 t x05 x07 x25 x35 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u6 (And.intro u5 (And.intro u1 (And.intro u3 (And.intro u0 u2)))))))) h

theorem clause14578 (t x01 x03 x05 x12 x13 x16 x26 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x67) + x68) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x26)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x12 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x67) + x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x16 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8995 t x01 x03 x05 x12 x13 x16 x26 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u3 (And.intro u10 (And.intro u2 (And.intro u4 (And.intro u0 (And.intro u5 (And.intro u9 (And.intro u1 (And.intro u6 u8)))))))))))) h

theorem clause14579 (t x01 x14 x16 x46 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x46)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ (x14 ≥ 0)) ∨ (¬ ((x16 + ((-1) * x68)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x14 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8996 t x01 x14 x16 x46 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u2 u6)))))))) h

theorem clause14580 (t x01 x03 x05 x12 x13 x16 x26 x57 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x26)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x12 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x26 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x68) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x16 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th8997 t x01 x03 x05 x12 x13 x16 x26 x57 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u10 (And.intro u3 (And.intro u5 (And.intro u9 (And.intro u4 (And.intro u7 (And.intro u6 u8)))))))))))) h

theorem clause14581 (t x02 x06 x23 x24 x26 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x23) + x24) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x06)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x23) + x24) ≥ 1) := by
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
  have u4 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th8999 t x02 x06 x23 x24 x26 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u3 (And.intro u1 u5)))))))) h

theorem clause14582 (t x02 x24 x26 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x24 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x24 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9000 t x02 x24 x26 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u5 (And.intro u4 u6)))))))) h

theorem clause14583 (t x02 x12 x23 x26 x34 x35 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ (x34 ≥ 0)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x26 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x26 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th9002 t x02 x12 x23 x26 x34 x35 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u6 (And.intro u7 (And.intro u3 (And.intro u2 (And.intro u5 (And.intro u8 u1)))))))))) h

theorem clause14584 (t x02 x06 x12 x24 x25 x26 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x24 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x06 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + ((-1) * x67) + x68) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
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
  have u3 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x06 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x67) + x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th9004 t x02 x06 x12 x24 x25 x26 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u6 (And.intro u7 (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u10 (And.intro u5 u9)))))))))))) h

theorem clause14585 (t x35 x45 x47 x56 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x35 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x57)) ≤ 0)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x47)) ≥ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x35 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9005 t x35 x45 x47 x56 x57 x78
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u6 (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u3 u2))))))) h

theorem clause14586 (t x02 x04 x12 x24 x25 x35 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x12) ≥ 1)) ∨ (¬ ((t + x35 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x02) + x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x35 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th9006 t x02 x04 x12 x24 x25 x35 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u7 (And.intro u8 (And.intro u1 (And.intro u4 (And.intro u2 (And.intro u6 u5)))))))))) h

theorem clause14587 (t x06 x12 x24 x26 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x24 ≥ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x26)) ≥ 0)) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x24 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x24)) ≥ 1) := by
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
  have h := NineTheoryTrial.th9007 t x06 x12 x24 x26 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u2 (And.intro u0 (And.intro u7 (And.intro u1 (And.intro u3 u6))))))))) h

theorem clause14588 (t x02 x12 x24 x25 x26 x57 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x24 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
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
  have u4 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x68)) ≤ (-1)) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th9008 t x02 x12 x24 x25 x26 x57 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u6 (And.intro u1 (And.intro u9 (And.intro u7 (And.intro u5 (And.intro u0 (And.intro u8 u2))))))))))) h

theorem clause14589 (t x02 x25 x26 x35 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x25) + x35) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x56)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x25) + x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th9009 t x02 x25 x26 x35 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u4 u5))))))) h

theorem clause14590 (t x02 x03 x05 x12 x23 x24 x26 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((t + ((-1) * x23) + x24) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x67) + x68) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x23) + x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((t + ((-1) * x67) + x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th9010 t x02 x03 x05 x12 x23 x24 x26 x56 x67 x68
  exact (fun hh => (fun hh => hh u7) (hh (And.intro u6 (And.intro u2 (And.intro u4 (And.intro u5 (And.intro u8 (And.intro u1 (And.intro u3 (And.intro u10 (And.intro u0 u9))))))))))) h

theorem clause14591 (t x12 x16 x24 x26 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x24 ≥ 0)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x16)) ≤ 0)) ∨ (¬ ((x16 + ((-1) * x68)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x24 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x16 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th9011 t x12 x16 x24 x26 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u5 (And.intro u3 (And.intro u2 (And.intro u6 u7))))))))) h

theorem clause14592 (t x05 x12 x15 x23 x24 x25 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x23) + x24) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x15)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x23) + x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x24)) ≥ 1) := by
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
  have h := NineTheoryTrial.th9015 t x05 x12 x15 x23 x24 x25 x57
  exact (fun hh => (fun hh => hh u7) (hh (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u6 (And.intro u4 u3)))))))) h

theorem clause14593 (t x02 x24 x26 x27 x47 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x24 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x27)) ≤ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x47)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x24 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x27)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x27 + ((-1) * x47)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th9017 t x02 x24 x26 x27 x47 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u3 (And.intro u6 (And.intro u8 (And.intro u4 u7)))))))))) h

theorem clause14594 (t x06 x24 x35 x45 x46 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x35 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x56)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x35 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9018 t x06 x24 x35 x45 x46 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u6 (And.intro u3 u0)))))))) h

theorem clause14595 (t x01 x02 x13 x24 x37 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((t + x37 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x37 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th9019 t x01 x02 x13 x24 x37 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u6 (And.intro u0 (And.intro u5 (And.intro u7 (And.intro u3 u2))))))))) h

theorem clause14596 (t x02 x12 x13 x23 x26 x34 x47 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((t + ((-1) * x02) + x12) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((t + x47 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
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
  have u3 : ((t + ((-1) * x02) + x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x47 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th9020 t x02 x12 x13 x23 x26 x34 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u5 (And.intro u4 (And.intro u8 (And.intro u0 (And.intro u3 (And.intro u7 u6)))))))))) h

theorem clause14598 (t x12 x24 x26 x45 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9023 t x12 x24 x26 x45 x67
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u5 (And.intro u4 (And.intro u2 (And.intro u0 (And.intro u3 u1))))))) h

theorem clause14599 (x23 x35 x36 : ℝ) : ((¬ ((x35 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ ((x23 + ((-1) * x36)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x23 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th9024 x23 x35 x36
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause14600 (t x02 x04 x12 x24 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x02 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x02 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th9026 t x02 x04 x12 x24 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u4 u3))))))) h

theorem clause14601 (t x05 x14 x34 x35 x45 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x14) + x34) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1)))) := by
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
  have u3 : ((x05 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9034 t x05 x14 x34 x35 x45 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u5 (And.intro u3 (And.intro u2 u6)))))))) h

theorem clause14602 (t x04 x06 x14 x17 x27 x45 x46 x47 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x46 ≥ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ ((t + ((-1) * x14)) ≤ 0) ∨ (¬ ((x17 + ((-1) * x67)) ≥ 0)) ∨ (¬ ((t + ((-1) * x27) + x47) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
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
  have u6 : (x46 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x14)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x17 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((t + ((-1) * x27) + x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th9035 t x04 x06 x14 x17 x27 x45 x46 x47 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u7 (And.intro u6 (And.intro u4 (And.intro u10 (And.intro u11 (And.intro u5 (And.intro u9 u1))))))))))))) h

theorem clause14603 (t x01 x03 x12 x27 x35 x58 x78 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((t + x58 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1)))) := by
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
  have u3 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x58 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x58)) ≥ 1) := by
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
  have h := NineTheoryTrial.th9036 t x01 x03 x12 x27 x35 x58 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u1 (And.intro u4 (And.intro u5 u6))))))))) h

theorem clause14604 (t x02 x12 x23 x26 x27 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((t + ((-1) * x23) + x26) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x23) + x26) ≥ 1) := by
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
  have h := NineTheoryTrial.th9039 t x02 x12 x23 x26 x27
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u3 (And.intro u4 u1))))))) h

theorem clause14606 (t x02 x07 x23 x26 x27 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((t + ((-1) * x23) + x26) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x27)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x23) + x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x27)) ≥ 0) := by
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
  have h := NineTheoryTrial.th9045 t x02 x07 x23 x26 x27 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u3 u6)))))))) h

theorem clause14607 (t x02 x04 x13 x14 x23 x26 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((t + ((-1) * x23) + x26) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x23) + x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th9048 t x02 x04 x13 x14 x23 x26 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u1 (And.intro u3 (And.intro u6 u7))))))))) h

theorem clause14608 (t x01 x02 x03 x12 x26 x27 x35 x57 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x27) + x57) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
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
  have u3 : ((t + x01 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x02)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x27) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th9050 t x01 x02 x03 x12 x26 x27 x35 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u1 (And.intro u5 (And.intro u7 (And.intro u4 (And.intro u3 (And.intro u0 (And.intro u2 u8)))))))))) h

theorem clause14609 (t x02 x03 x26 x34 x45 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + x02 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
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
  have u3 : ((t + x02 + ((-1) * x03)) ≥ 1) := by
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
  have h := NineTheoryTrial.th9052 t x02 x03 x26 x34 x45 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u6 (And.intro u7 (And.intro u5 (And.intro u0 (And.intro u2 (And.intro u1 u3))))))))) h

theorem clause14610 (t x02 x03 x06 x26 x34 x45 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + x02 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((t + ((-1) * x26) + x56) ≥ 1))) := by
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
  have u3 : ((t + x02 + ((-1) * x03)) ≥ 1) := by
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
  have u6 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x26) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th9053 t x02 x03 x06 x26 x34 x45 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u7 (And.intro u1 (And.intro u4 (And.intro u3 (And.intro u8 (And.intro u6 (And.intro u0 u2)))))))))) h

theorem clause14611 (t x02 x12 x14 x26 x45 x58 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((t + x58 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((t + x12 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x58 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x12 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x58)) ≥ 1) := by
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
  have u8 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th9057 t x02 x12 x14 x26 x45 x58 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u7 (And.intro u5 (And.intro u1 (And.intro u6 (And.intro u3 (And.intro u4 (And.intro u8 u0)))))))))) h

theorem clause14612 (t x14 x24 x34 : ℝ) : ((¬ ((t + ((-1) * x14) + x34) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x34)) ≥ 0)) ∨ ((t + ((-1) * x14) + x24) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x14) + x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x14) + x24) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th9061 t x14 x24 x34
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause14614 (t x03 x12 x23 x35 x57 x78 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≤ 0)) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
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
  have u4 : ((x03 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th9067 t x03 x12 x23 x35 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u4 (And.intro u1 (And.intro u0 (And.intro u7 (And.intro u6 (And.intro u3 u5))))))))) h

theorem clause14615 (t x02 x03 x23 x24 x35 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x23) + x24) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x23) + x24) ≥ 1) := by
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
  have u5 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th9068 t x02 x03 x23 x24 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u3 (And.intro u2 (And.intro u5 (And.intro u0 u1))))))) h

theorem clause14616 (t x06 x12 x25 x35 x46 x56 x58 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1))) ∨ (¬ (x06 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x46) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x35 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : (x06 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th9069 t x06 x12 x25 x35 x46 x56 x58 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u9 (And.intro u4 (And.intro u8 (And.intro u3 (And.intro u1 (And.intro u6 (And.intro u0 (And.intro u7 u5))))))))))) h

theorem clause14617 (t x01 x03 x16 x35 x46 x56 x67 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1)))) := by
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
  have u3 : ((t + ((-1) * x46) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x67)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th9070 t x01 x03 x16 x35 x46 x56 x67
  exact (fun hh => (fun hh => hh u7) (hh (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u4 (And.intro u3 (And.intro u5 u6)))))))) h

theorem clause14618 (t x01 x03 x04 x12 x23 x35 x47 x57 x67 x78 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≤ 0)) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
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
  have u4 : ((x03 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th9072 t x01 x03 x04 x12 x23 x35 x47 x57 x67 x78
  exact (fun hh => (fun hh => hh u11) (hh (And.intro u5 (And.intro u4 (And.intro u10 (And.intro u3 (And.intro u8 (And.intro u0 (And.intro u1 (And.intro u7 (And.intro u9 (And.intro u6 u2)))))))))))) h

theorem clause14620 (t x14 x45 x47 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ (x57 ≥ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x57 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9078 t x14 x45 x47 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u6 (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u2 u5)))))))) h

theorem clause14621 (t x01 x03 x14 x37 x47 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x47) + x57) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x47) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
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
  have u5 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x03 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th9079 t x01 x03 x14 x37 x47 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u7 (And.intro u1 (And.intro u4 (And.intro u3 (And.intro u2 (And.intro u6 u5))))))))) h

theorem clause14622 (t x02 x24 x26 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x45) + x46) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x45) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th9081 t x02 x24 x26 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u4 (And.intro u3 (And.intro u5 (And.intro u1 u0))))))) h

theorem clause14623 (t x02 x12 x23 x24 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ (x46 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x46 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9082 t x02 x12 x23 x24 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u5 (And.intro u2 u6)))))))) h

theorem clause14624 (t x02 x14 x24 x26 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x45) + x46) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x45) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x26 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9083 t x02 x14 x24 x26 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u6 (And.intro u2 (And.intro u1 (And.intro u0 u4)))))))) h

theorem clause14625 (x25 x35 x57 : ℝ) : ((¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x35)) ≥ 0)) ∨ ((x25 + ((-1) * x57)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x25 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x25 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th9085 x25 x35 x57
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause14626 (t x02 x12 x23 x25 x35 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x25 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
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
  have u3 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th9088 t x02 x12 x23 x25 x35 x57 x78
  exact (fun hh => (fun hh => hh u7) (hh (And.intro u5 (And.intro u6 (And.intro u2 (And.intro u3 (And.intro u8 (And.intro u4 (And.intro u1 u0))))))))) h

theorem clause14627 (t x12 x23 x27 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ (x57 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x57 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9089 t x12 x23 x27 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u4 (And.intro u6 (And.intro u0 (And.intro u5 (And.intro u1 u3)))))))) h

theorem clause14628 (t x01 x14 x16 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x45) + x46) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x45) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th9090 t x01 x14 x16 x45 x46
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u2 (And.intro u1 (And.intro u5 (And.intro u4 u0)))))) h

theorem clause14629 (t x01 x03 x14 x23 x24 x34 x35 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((t + ((-1) * x24) + x34) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ (x01 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x24) + x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th9091 t x01 x03 x14 x23 x24 x34 x35 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u0 (And.intro u3 (And.intro u6 (And.intro u4 (And.intro u9 (And.intro u8 (And.intro u1 u7))))))))))) h

theorem clause14631 (t x01 x03 x13 x16 x35 x36 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ ((t + ((-1) * x13)) ≤ 0) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + x36 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x36 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th9094 t x01 x03 x13 x16 x35 x36 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u9 (And.intro u5 (And.intro u0 (And.intro u7 (And.intro u8 (And.intro u4 (And.intro u6 (And.intro u2 u3))))))))))) h

theorem clause14632 (t x02 x12 x24 x26 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ (x02 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9095 t x02 x12 x24 x26 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u6 (And.intro u5 (And.intro u4 (And.intro u2 u1)))))))) h

theorem clause14633 (t x02 x12 x14 x24 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((t + x02 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x02 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th9097 t x02 x12 x14 x24 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u3 u5))))))) h

theorem clause14634 (t x03 x13 x34 x35 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ ((t + ((-1) * x13)) ≤ 0) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ (x46 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9098 t x03 x13 x34 x35 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u1 (And.intro u6 u5)))))))) h

theorem clause14635 (t x01 x14 x46 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
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
  have u4 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9099 t x01 x14 x46 x67 x78
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u4 (And.intro u3 (And.intro u2 (And.intro u6 (And.intro u5 u0))))))) h

theorem clause14636 (t x01 x03 x17 x35 x57 x67 x78 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
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
  have u3 : ((t + x01 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th9102 t x01 x03 x17 x35 x57 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u1 (And.intro u2 (And.intro u3 (And.intro u6 (And.intro u5 u7))))))))) h

theorem clause14637 (t x01 x03 x12 x13 x16 x26 x35 x57 x67 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x26)) ≤ 0))) := by
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
  have u3 : ((t + x12 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x16 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th9103 t x01 x03 x12 x13 x16 x26 x35 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u9 (And.intro u6 (And.intro u0 (And.intro u8 (And.intro u1 (And.intro u7 (And.intro u2 (And.intro u4 u3))))))))))) h

theorem clause14638 (t x01 x02 x03 x12 x23 x24 x35 x57 x78 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
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
  have u3 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x01 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x02)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th9104 t x01 x02 x03 x12 x23 x24 x35 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u3 (And.intro u7 (And.intro u8 (And.intro u6 (And.intro u0 (And.intro u5 (And.intro u10 (And.intro u2 u9)))))))))))) h

theorem clause14640 (t x02 x12 x14 x23 x24 x26 x46 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ (x02 ≥ 0)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x26 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((t + ((-1) * x67) + x68) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
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
  have u3 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x14 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x26 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x67) + x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th9108 t x02 x12 x14 x23 x24 x26 x46 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u6 (And.intro u7 (And.intro u10 (And.intro u9 (And.intro u3 (And.intro u4 u2)))))))))))) h

theorem clause14641 (t x01 x02 x03 x13 x14 x24 x35 x38 x46 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ ((t + ((-1) * x13)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x24)) ≥ 0)) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((t + x38 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x38)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x02)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x14 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((t + x38 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x03 + ((-1) * x38)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th9109 t x01 x02 x03 x13 x14 x24 x35 x38 x46 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u5 (And.intro u11 (And.intro u2 (And.intro u10 (And.intro u4 (And.intro u7 (And.intro u6 (And.intro u8 u9))))))))))))) h

theorem clause14642 (t x03 x12 x23 x28 x34 x38 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ (x34 ≥ 0)) ∨ (¬ ((x28 + ((-1) * x38)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x28)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x38)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x28 + ((-1) * x38)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x28)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x03 + ((-1) * x38)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th9110 t x03 x12 x23 x28 x34 x38
  exact (fun hh => (fun hh => hh u7) (hh (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u4 u6)))))))) h

theorem clause14643 (t x01 x02 x12 x27 x28 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x28 + ((-1) * x78)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x28)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x02)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x27)) ≥ 1) := by
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
  have u7 : ((x28 + ((-1) * x78)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x28)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th9111 t x01 x02 x12 x27 x28 x67 x78
  exact (fun hh => (fun hh => hh u8) (hh (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u6 (And.intro u5 (And.intro u2 u7))))))))) h

theorem clause14644 (t x01 x02 x03 x12 x13 x26 x27 x35 x37 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ ((t + ((-1) * x13)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1)) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x27) + x37) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x02)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x27) + x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th9112 t x01 x02 x03 x12 x13 x26 x27 x35 x37
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u4 (And.intro u9 (And.intro u6 (And.intro u7 (And.intro u3 (And.intro u10 (And.intro u5 u8)))))))))))) h

theorem clause14645 (t x03 x27 x34 x37 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ (x34 ≥ 0)) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1))) ∨ ((t + ((-1) * x27)) ≤ 0) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9113 t x03 x27 x34 x37 x78
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u6 (And.intro u5 (And.intro u1 (And.intro u2 (And.intro u0 u4))))))) h

theorem clause14646 (t x01 x02 x12 x13 x26 x27 x37 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x13)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((t + ((-1) * x27) + x57) ≥ 1)) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x02)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x27) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x12 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th9114 t x01 x02 x12 x13 x26 x27 x37 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u8 (And.intro u2 (And.intro u10 (And.intro u3 (And.intro u9 (And.intro u1 (And.intro u7 (And.intro u6 u5)))))))))))) h

theorem clause14647 (t x01 x02 x05 x14 x24 x46 x57 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x05)) ≥ 1)) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x02)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x01 + ((-1) * x05)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x68) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th9116 t x01 x02 x05 x14 x24 x46 x57 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u4 (And.intro u8 (And.intro u0 (And.intro u7 (And.intro u6 (And.intro u3 (And.intro u9 (And.intro u5 u1))))))))))) h

theorem clause14648 (t x01 x12 x26 x45 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th9117 t x01 x12 x26 x45 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u7 (And.intro u1 u5))))))))) h

theorem clause14649 (t x01 x02 x12 x24 x26 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x02)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th9118 t x01 x02 x12 x24 x26 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u0 (And.intro u7 (And.intro u6 (And.intro u1 (And.intro u2 u4))))))))) h

theorem clause14650 (t x01 x12 x24 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ (x01 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9119 t x01 x12 x24 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u0 (And.intro u5 (And.intro u6 (And.intro u2 u4)))))))) h

theorem clause14651 (t x03 x07 x13 x37 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x03 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x03 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x07)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th9120 t x03 x07 x13 x37 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u5 (And.intro u4 u2))))))) h

theorem clause14652 (t x01 x03 x17 x23 x27 x35 x37 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1)) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x27) + x37) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
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
  have u5 : ((x03 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x27) + x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th9123 t x01 x03 x17 x23 x27 x35 x37 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u1 (And.intro u5 (And.intro u8 (And.intro u6 (And.intro u2 (And.intro u9 (And.intro u4 (And.intro u0 u3))))))))))) h

theorem clause14653 (t x02 x03 x12 x23 x35 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((t + x02 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1)))) := by
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
  have u3 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th9126 t x02 x03 x12 x23 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u1 (And.intro u3 u5))))))) h

theorem clause14654 (t x01 x12 x16 x24 x26 x45 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th9127 t x01 x12 x16 x24 x26 x45 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u1 (And.intro u6 (And.intro u8 (And.intro u5 (And.intro u2 (And.intro u3 u7)))))))))) h

theorem clause14655 (t x01 x12 x24 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ ((t + ((-1) * x78)) ≤ 0)) := by
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
  have u3 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9130 t x01 x12 x24 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u1 u6)))))))) h

theorem clause14656 (t x02 x03 x12 x23 x24 x26 x35 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ (x02 ≥ 0)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((t + ((-1) * x26) + x36) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x26) + x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th9131 t x02 x03 x12 x23 x24 x26 x35 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u4 (And.intro u6 (And.intro u2 (And.intro u7 (And.intro u8 (And.intro u9 (And.intro u1 u5))))))))))) h

theorem clause14657 (t x01 x14 x24 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ (x01 ≥ 0))) := by
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
  have u3 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9133 t x01 x14 x24 x45 x46
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u3 (And.intro u0 (And.intro u6 (And.intro u4 (And.intro u2 u5))))))) h

theorem clause14658 (t x01 x03 x05 x14 x35 x46 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x46) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th9135 t x01 x03 x05 x14 x35 x46 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u8 (And.intro u3 (And.intro u7 (And.intro u4 (And.intro u1 u6)))))))))) h

theorem clause14659 (t x07 x26 x35 x56 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x07 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + ((-1) * x26) + x56) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x07 + ((-1) * x57)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x07 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x26) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9137 t x07 x26 x35 x56 x57 x67
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u4 (And.intro u2 (And.intro u6 (And.intro u5 (And.intro u0 u1))))))) h

theorem clause14660 (t x01 x03 x05 x12 x26 x35 x56 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th9138 t x01 x03 x05 x12 x26 x35 x56 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u5 (And.intro u9 (And.intro u8 (And.intro u1 (And.intro u6 (And.intro u7 u10)))))))))))) h

theorem clause14661 (t x01 x03 x05 x12 x13 x14 x35 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((t + x35 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x12 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x35 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th9141 t x01 x03 x05 x12 x13 x14 x35 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u7 (And.intro u3 (And.intro u6 (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u9 (And.intro u8 u2))))))))))) h

theorem clause14662 (t x02 x12 x23 x24 x25 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ (x24 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9143 t x02 x12 x23 x24 x25
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u6 (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u2 u1)))))))) h

theorem clause14663 (t x02 x03 x05 x12 x23 x24 x26 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x24 ≥ 0)) ∨ (¬ ((x03 + ((-1) * x23)) ≤ 0)) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x67) + x68) ≥ 1))) := by
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
  have u3 : (x24 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x03 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((t + ((-1) * x67) + x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th9150 t x02 x03 x05 x12 x23 x24 x26 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u11 (And.intro u5 (And.intro u0 (And.intro u4 (And.intro u7 (And.intro u2 (And.intro u6 (And.intro u3 (And.intro u1 (And.intro u8 (And.intro u10 u9))))))))))))) h

theorem clause14664 (t x02 x05 x12 x16 x23 x24 x25 x26 x57 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x24 ≥ 0)) ∨ (¬ ((x05 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x25)) ≥ 0)) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x16 + ((-1) * x68)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x05 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((t + ((-1) * x68) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x16 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))))
  have u12 : ((x16 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))))
  have h := NineTheoryTrial.th9151 t x02 x05 x12 x16 x23 x24 x25 x26 x57 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u9 (And.intro u12 (And.intro u11 (And.intro u8 (And.intro u7 (And.intro u6 (And.intro u0 (And.intro u2 (And.intro u10 (And.intro u5 (And.intro u1 (And.intro u3 u4)))))))))))))) h

theorem clause14666 (t x35 x45 x47 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x35 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x47)) ≥ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x35 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th9154 t x35 x45 x47 x57 x78
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u3 (And.intro u4 (And.intro u2 (And.intro u1 u0)))))) h

theorem clause14667 (t x01 x03 x05 x12 x26 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x67) + x68) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x01 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x67) + x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th9155 t x01 x03 x05 x12 x26 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u5 (And.intro u3 (And.intro u7 (And.intro u6 (And.intro u0 (And.intro u2 (And.intro u4 u1)))))))))) h

theorem clause14668 (x16 x26 x67 : ℝ) : ((¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ ((x16 + ((-1) * x67)) ≤ (-1)) ∨ (¬ ((x16 + ((-1) * x26)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x16 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th9157 x16 x26 x67
  exact (fun hh => u1 (hh (And.intro u0 u2))) h

theorem clause14670 (t x14 x34 x35 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x14) + x34) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x57)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
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
  have u4 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9160 t x14 x34 x35 x45 x56 x57
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u2 (And.intro u5 (And.intro u1 (And.intro u6 (And.intro u0 u3))))))) h

theorem clause14671 (t x01 x02 x05 x12 x24 x25 x35 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ (¬ ((t + ((-1) * x25) + x35) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((t + x01 + ((-1) * x05)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x02)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x25) + x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x01 + ((-1) * x05)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th9161 t x01 x02 x05 x12 x24 x25 x35 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u3 (And.intro u6 (And.intro u4 (And.intro u0 (And.intro u8 (And.intro u7 u1)))))))))) h

theorem clause14672 (t x06 x24 x26 x45 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x45) + x46) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x45) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9162 t x06 x24 x26 x45 x46 x67
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u3 (And.intro u4 (And.intro u6 (And.intro u2 (And.intro u5 u0))))))) h

theorem clause14674 (t x05 x34 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ (x34 ≥ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ ((t + ((-1) * x57)) ≤ 0)) := by
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
  have u3 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9164 t x05 x34 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u5 (And.intro u2 u3)))))))) h

theorem clause14675 (t x05 x35 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + x35 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
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
  have u3 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th9165 t x05 x35 x45 x56 x57
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u2 u4)))))) h

theorem clause14677 (t x05 x23 x35 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9167 t x05 x23 x35 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u6 (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u1 u2)))))))) h

theorem clause14678 (t x12 x23 x25 x35 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x25 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ (¬ (x45 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x25 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th9169 t x12 x23 x25 x35 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u5 (And.intro u0 (And.intro u3 (And.intro u4 (And.intro u2 (And.intro u1 u6))))))))) h

theorem clause14680 (t x15 x34 x45 x46 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((x15 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x45)) ≥ 0) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9173 t x15 x34 x45 x46 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u6 (And.intro u5 (And.intro u1 (And.intro u2 u3)))))))) h

theorem clause14681 (t x01 x03 x12 x25 x35 x45 x56 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x25) + x45) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1)))) := by
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
  have u3 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x25) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th9174 t x01 x03 x12 x25 x35 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u7 (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u5 (And.intro u6 u4))))))))) h

theorem clause14683 (t x01 x02 x12 x13 x15 x25 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1)))) := by
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
  have u3 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
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
  have u7 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th9177 t x01 x02 x12 x13 x15 x25 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u8 (And.intro u6 (And.intro u5 (And.intro u7 u3)))))))))) h

theorem clause14684 (t x01 x14 x15 x24 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((t + x14 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x14 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th9178 t x01 x14 x15 x24 x45
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u2 (And.intro u4 (And.intro u3 (And.intro u0 u1)))))) h

theorem clause14685 (t x14 x45 x47 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x57)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x56 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th9180 t x14 x45 x47 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u3 u1))))))) h

theorem clause14686 (t x01 x02 x12 x13 x15 x26 x45 x56 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
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
  have u3 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x45)) ≥ 0) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th9182 t x01 x02 x12 x13 x15 x26 x45 x56 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u1 (And.intro u7 (And.intro u0 (And.intro u4 (And.intro u9 (And.intro u5 (And.intro u6 (And.intro u2 (And.intro u3 (And.intro u10 u11))))))))))))) h

theorem clause14687 (t x01 x02 x14 x25 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≥ 1) := by
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
  have u6 : ((t + x56 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th9184 t x01 x02 x14 x25 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u5 (And.intro u7 (And.intro u1 (And.intro u6 u3))))))))) h

theorem clause14688 (t x01 x13 x14 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x13)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
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
  have u5 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9185 t x01 x13 x14 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u6 (And.intro u4 (And.intro u5 (And.intro u1 u2)))))))) h

theorem clause14689 (t x03 x05 x13 x14 x34 x35 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x14 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((t + ((-1) * x03) + x13) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x03) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x56 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th9186 t x03 x05 x13 x14 x34 x35 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u7 (And.intro u3 (And.intro u6 (And.intro u9 (And.intro u2 (And.intro u0 (And.intro u8 u4))))))))))) h

theorem clause14690 (t x05 x56 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9187 t x05 x56 x57 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u4 (And.intro u3 (And.intro u6 u2)))))))) h

theorem clause14691 (t x14 x24 x25 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((t + x14 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x14 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th9188 t x14 x24 x25 x45 x57
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u2 (And.intro u4 (And.intro u0 (And.intro u1 u3)))))) h

theorem clause14692 (t x01 x02 x03 x04 x13 x24 x34 x35 x45 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((t + ((-1) * x24) + x34) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x24) + x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th9190 t x01 x02 x03 x04 x13 x24 x34 x35 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u0 (And.intro u6 (And.intro u2 (And.intro u1 (And.intro u7 (And.intro u3 (And.intro u9 u8))))))))))) h

theorem clause14693 (t x01 x03 x12 x25 x35 x56 x57 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1)))) := by
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
  have u3 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x56 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th9192 t x01 x03 x12 x25 x35 x56 x57
  exact (fun hh => (fun hh => hh u7) (hh (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u2 (And.intro u5 (And.intro u6 u1)))))))) h

theorem clause14694 (t x01 x13 x15 x35 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x13)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x35)) ≥ 0)) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th9195 t x01 x13 x15 x35 x45 x56
  exact (fun hh => (fun hh => hh u7) (hh (And.intro u5 (And.intro u3 (And.intro u6 (And.intro u2 (And.intro u1 (And.intro u0 u4)))))))) h

theorem clause14695 (t x01 x13 x34 x35 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ (x45 ≥ 0)) ∨ ((t + ((-1) * x01)) ≤ 0)) := by
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
  have u3 : ((x34 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th9197 t x01 x13 x34 x35 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u3 (And.intro u0 (And.intro u6 (And.intro u5 (And.intro u4 (And.intro u1 u2))))))))) h

theorem clause14696 (t x03 x06 x13 x36 x37 x47 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x03) + x13) ≥ 1)) ∨ (¬ ((t + x47 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x03) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x47 + ((-1) * x67)) ≥ 1) := by
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
  have u5 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x03 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th9198 t x03 x06 x13 x36 x37 x47 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u3 (And.intro u0 (And.intro u6 (And.intro u5 (And.intro u2 (And.intro u8 u7)))))))))) h

theorem clause14697 (t x02 x05 x23 x25 x26 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((t + ((-1) * x23) + x26) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x23) + x26) ≥ 1) := by
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
  have h := NineTheoryTrial.th9200 t x02 x05 x23 x25 x26 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u4 (And.intro u1 (And.intro u0 (And.intro u6 u2)))))))) h

theorem clause14698 (t x01 x04 x13 x35 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x04) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1)))) := by
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
  have u3 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x01) + x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x56 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th9201 t x01 x04 x13 x35 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u3 (And.intro u7 (And.intro u1 (And.intro u6 (And.intro u0 (And.intro u5 u2))))))))) h

theorem clause14699 (t x02 x23 x24 x25 x35 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x23) + x24) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x23) + x24) ≥ 1) := by
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
  have u4 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x56)) ≥ 1) := by
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
  have h := NineTheoryTrial.th9203 t x02 x23 x24 x25 x35 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u6 (And.intro u2 (And.intro u8 (And.intro u5 u0)))))))))) h

theorem clause14700 (t x02 x06 x12 x23 x25 x26 x35 x46 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x25 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x23) + x26) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x26)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x25 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x06 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((t + ((-1) * x23) + x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))))
  have u12 : ((x06 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))))
  have h := NineTheoryTrial.th9204 t x02 x06 x12 x23 x25 x26 x35 x46 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u9 (And.intro u0 (And.intro u4 (And.intro u1 (And.intro u3 (And.intro u7 (And.intro u8 (And.intro u6 (And.intro u10 (And.intro u12 u11)))))))))))))) h

theorem clause14701 (t x05 x06 x36 x45 x57 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x36 ≥ 0)) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x06)) ≥ 0)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x06 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x36 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x05 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th9205 t x05 x06 x36 x45 x57 x68
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u7 (And.intro u3 (And.intro u6 (And.intro u4 (And.intro u1 (And.intro u0 u2)))))))) h

theorem clause14702 (t x02 x05 x12 x13 x23 x25 x35 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((t + ((-1) * x02) + x12) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x25)) ≥ 0)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x02) + x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x25)) ≥ 0) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th9207 t x02 x05 x12 x13 x23 x25 x35 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u8 (And.intro u6 (And.intro u10 (And.intro u11 (And.intro u7 (And.intro u5 (And.intro u3 (And.intro u4 (And.intro u1 (And.intro u9 u2))))))))))))) h

theorem clause14704 (t x01 x06 x12 x25 x35 x46 x56 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x06) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x25 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x46) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x01) + x06) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x06 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th9215 t x01 x06 x12 x25 x35 x46 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u1 (And.intro u5 (And.intro u8 (And.intro u3 (And.intro u6 (And.intro u7 u4)))))))))) h

theorem clause14705 (t x02 x04 x23 x24 x25 x35 x46 x56 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x23) + x24) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x23) + x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x25 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th9216 t x02 x04 x23 x24 x25 x35 x46 x56 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u10 (And.intro u5 (And.intro u11 (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u6 (And.intro u7 (And.intro u8 (And.intro u9 (And.intro u3 u4))))))))))))) h

theorem clause14706 (t x02 x03 x12 x23 x25 x35 x56 x57 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((t + x02 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1)))) := by
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
  have u3 : ((t + x02 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x56)) ≥ 1) := by
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
  have h := NineTheoryTrial.th9220 t x02 x03 x12 x23 x25 x35 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u2 (And.intro u5 (And.intro u0 (And.intro u7 (And.intro u6 u8)))))))))) h

theorem clause14707 (t x02 x03 x23 x24 x25 x35 x56 x57 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x23) + x24) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x23) + x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x56)) ≥ 1) := by
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
  have h := NineTheoryTrial.th9222 t x02 x03 x23 x24 x25 x35 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u7 (And.intro u6 (And.intro u8 u3)))))))))) h

theorem clause14708 (t x01 x02 x15 x24 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
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
  have u4 : ((t + x56 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th9223 t x01 x02 x15 x24 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u5 (And.intro u7 u6))))))))) h

theorem clause14712 (t x02 x05 x12 x23 x24 x25 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x05 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ (x02 ≥ 0)) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x56 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th9232 t x02 x05 x12 x23 x24 x25 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u7 (And.intro u4 (And.intro u3 (And.intro u9 (And.intro u6 (And.intro u2 (And.intro u1 (And.intro u5 (And.intro u8 u10)))))))))))) h

theorem clause14713 (t x04 x13 x24 x34 x46 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ ((x04 + ((-1) * x24)) ≥ 0) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((x04 + ((-1) * x24)) ≥ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th9234 t x04 x13 x24 x34 x46 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u1 (And.intro u6 (And.intro u2 (And.intro u8 (And.intro u7 (And.intro u3 u5)))))))))) h

theorem clause14714 (t x03 x34 x35 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ (x34 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x34 ≥ 0) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9236 t x03 x34 x35 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u6 (And.intro u3 (And.intro u2 (And.intro u4 u1)))))))) h

theorem clause14715 (t x02 x05 x23 x24 x25 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x23) + x24) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
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
  have u3 : ((x02 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x24)) ≥ 1) := by
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
  have h := NineTheoryTrial.th9237 t x02 x05 x23 x24 x25 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u1 (And.intro u6 (And.intro u3 (And.intro u0 u4)))))))) h

theorem clause14716 (t x05 x13 x23 x25 x35 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x13 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x13 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x35)) ≥ 0) := by
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
  have h := NineTheoryTrial.th9239 t x05 x13 x23 x25 x35 x57
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u2 (And.intro u1 (And.intro u5 (And.intro u0 (And.intro u4 u6))))))) h

theorem clause14717 (t x01 x12 x15 x23 x25 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x25)) ≥ 0)) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x12 ≥ 0) := by
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
  have u7 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th9240 t x01 x12 x15 x23 x25 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u7 (And.intro u4 (And.intro u6 u5))))))))) h

theorem clause14718 (t x01 x02 x12 x13 x15 x24 x35 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x12 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x15 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th9241 t x01 x02 x12 x13 x15 x24 x35 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u4 (And.intro u6 (And.intro u1 (And.intro u7 (And.intro u2 (And.intro u3 (And.intro u8 (And.intro u11 (And.intro u9 u10))))))))))))) h

theorem clause14719 (t x01 x15 x16 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ (x16 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x16 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9244 t x01 x15 x16 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u4 u5)))))))) h

theorem clause14720 (t x01 x02 x17 x24 x46 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1))) := by
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
  have u3 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th9248 t x01 x02 x17 x24 x46 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u5 (And.intro u6 (And.intro u7 u1))))))))) h

theorem clause14721 (t x24 x34 x36 x45 x46 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ (x34 ≥ 0))) := by
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
  have u3 : ((x34 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th9252 t x24 x34 x36 x45 x46 x68
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u6 (And.intro u2 (And.intro u7 (And.intro u1 (And.intro u3 (And.intro u5 u0)))))))) h

theorem clause14722 (t x02 x12 x24 x25 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ (x02 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1))) ∨ ((t + ((-1) * x57)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≥ 0) := by
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
  have u5 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9253 t x02 x12 x24 x25 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u5 u6)))))))) h

theorem clause14723 (t x02 x03 x12 x23 x25 x35 x45 x57 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((t + x02 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((t + x35 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1)))) := by
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
  have u3 : ((t + x02 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x35 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th9257 t x02 x03 x12 x23 x25 x35 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u4 (And.intro u7 (And.intro u8 (And.intro u3 (And.intro u0 (And.intro u6 u5)))))))))) h

theorem clause14724 (t x02 x24 x26 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x24 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ ((t + ((-1) * x46)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x24 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x67)) ≥ 1) := by
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
  have h := NineTheoryTrial.th9261 t x02 x24 x26 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u3 u1)))))))) h

theorem clause14726 (t x05 x34 x45 x47 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((t + x05 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x57)) ≥ 0))) := by
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
  have u3 : ((t + x05 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th9266 t x05 x34 x45 x47 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u4 (And.intro u0 u5))))))) h

theorem clause14727 (t x02 x07 x23 x24 x25 x27 x37 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x23) + x24) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((t + x37 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x27)) ≥ 0)) ∨ (¬ ((x07 + ((-1) * x27)) ≤ 0)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x23) + x24) ≥ 1) := by
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
  have u4 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x37 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x23 + ((-1) * x27)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x07 + ((-1) * x27)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th9269 t x02 x07 x23 x24 x25 x27 x37 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u0 (And.intro u1 (And.intro u9 (And.intro u6 (And.intro u3 (And.intro u4 (And.intro u8 u7))))))))))) h

theorem clause14728 (t x02 x12 x15 x25 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x12) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x15)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x02) + x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th9271 t x02 x12 x15 x25 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u4 (And.intro u0 (And.intro u1 u3))))))) h

theorem clause14730 (x15 x25 x56 : ℝ) : (((x25 + ((-1) * x56)) ≥ 1) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x25)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x15 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th9276 x15 x25 x56
  exact (fun hh => u0 (hh (And.intro u2 u1))) h

theorem clause14731 (t x01 x02 x05 x23 x27 x35 x37 x45 x56 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ (¬ (x35 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((t + x37 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x27)) ≥ 0)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x02)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x37 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x23 + ((-1) * x27)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))))
  have u12 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))))
  have h := NineTheoryTrial.th9277 t x01 x02 x05 x23 x27 x35 x37 x45 x56 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u9 (And.intro u0 (And.intro u3 (And.intro u11 (And.intro u2 (And.intro u1 (And.intro u6 (And.intro u8 (And.intro u7 (And.intro u12 (And.intro u10 u4)))))))))))))) h

theorem clause14732 (x05 x45 x58 : ℝ) : ((¬ ((x05 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x05 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th9279 x05 x45 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause14734 (t x12 x23 x25 x35 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ (x35 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9284 t x12 x23 x25 x35 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u4 (And.intro u5 (And.intro u3 u6)))))))) h

theorem clause14735 (t x03 x05 x35 x37 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((t + x35 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x35 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th9285 t x03 x05 x35 x37 x56
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u4 u2)))))) h

theorem clause14736 (t x01 x03 x12 x13 x16 x37 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x68)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x12 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x68) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x16 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th9290 t x01 x03 x12 x13 x16 x37 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u6 (And.intro u7 (And.intro u8 (And.intro u4 u5)))))))))) h

theorem clause14738 (t x04 x34 x35 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + ((-1) * x04) + x34) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x04) + x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th9296 t x04 x34 x35 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u2 (And.intro u3 (And.intro u0 u1))))))) h

theorem clause14739 (t x05 x35 x56 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ (x35 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9299 t x05 x35 x56 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u0 (And.intro u2 (And.intro u5 (And.intro u1 (And.intro u3 u4)))))))) h

theorem clause14740 (t x01 x13 x15 x35 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x13)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ (x35 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9301 t x01 x13 x15 x35 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u0 (And.intro u2 (And.intro u6 (And.intro u1 u5)))))))) h

theorem clause14741 (t x01 x03 x05 x13 x34 x35 x37 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ (x35 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((t + x37 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ ((t + ((-1) * x01)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x35 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x37 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th9303 t x01 x03 x05 x13 x34 x35 x37 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u8 (And.intro u9 (And.intro u6 (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u10 (And.intro u2 (And.intro u3 u7)))))))))))) h

theorem clause14742 (t x15 x23 x35 x36 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((t + x15 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x56)) ≥ 0) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th9308 t x15 x23 x35 x36 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u3 (And.intro u0 (And.intro u2 u1))))))) h

theorem clause14743 (t x13 x23 x34 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9309 t x13 x23 x34 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u6 (And.intro u5 (And.intro u3 (And.intro u1 u2)))))))) h

theorem clause14744 (t x01 x02 x04 x14 x23 x36 x45 x47 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ (¬ (x45 ≥ 0))) := by
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
  have u3 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th9310 t x01 x02 x04 x14 x23 x36 x45 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u4 (And.intro u9 (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u7 (And.intro u8 (And.intro u1 (And.intro u3 u10)))))))))))) h

theorem clause14746 (t x01 x13 x47 x67 : ℝ) : ((¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ ((t + x47 + ((-1) * x67)) ≥ 1) ∨ (¬ ((x47 + ((-1) * x67)) ≥ 0)) ∨ ((t + ((-1) * x01)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + x47 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x47 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr hh))))
  have h := NineTheoryTrial.th9315 t x01 x13 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u2 u3)))))) h

theorem clause14747 (x13 x34 x35 : ℝ) : ((¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x35)) ≤ 0)) ∨ ((x13 + ((-1) * x35)) ≤ (-1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x13 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th9319 x13 x34 x35
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause14748 (t x14 x23 x34 x35 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x14 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x14 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th9322 t x14 x23 x34 x35 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u5 u2))))))) h

theorem clause14750 (t x05 x06 x15 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x06)) ≥ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x05) + x15) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x05 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x05) + x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th9326 t x05 x06 x15 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u1 u4))))))) h

theorem clause14751 (t x03 x23 x24 x34 x35 x45 x56 x57 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((t + x03 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x03 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x56) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th9328 t x03 x23 x24 x34 x35 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u6 (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u4 (And.intro u5 (And.intro u0 u7)))))))))) h

theorem clause14752 (t x04 x13 x14 x34 x35 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((t + ((-1) * x34) + x35) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x34) + x35) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9334 t x04 x13 x14 x34 x35 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u3 (And.intro u6 (And.intro u0 (And.intro u5 (And.intro u1 u2)))))))) h

theorem clause14753 (t x03 x23 x34 x35 x57 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ (x57 ≥ 0))) := by
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
  have u4 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x57 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9335 t x03 x23 x34 x35 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u6 (And.intro u1 (And.intro u5 (And.intro u0 (And.intro u2 u3)))))))) h

theorem clause14754 (t x03 x23 x34 x36 x46 x67 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ (x67 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th9336 t x03 x23 x34 x36 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u7 (And.intro u5 (And.intro u0 u6))))))))) h

theorem clause14755 (t x04 x13 x14 x23 x34 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((t + x13 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x13 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x34)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9339 t x04 x13 x14 x23 x34 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u3 (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u1 u2)))))))) h

theorem clause14756 (t x02 x03 x23 x25 x34 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + ((-1) * x23) + x25) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1))) := by
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
  have u3 : ((t + ((-1) * x23) + x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th9340 t x02 x03 x23 x25 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u2 u5))))))) h

theorem clause14757 (t x03 x25 x35 x36 x56 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x25) + x35) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1))) := by
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
  have u3 : ((t + ((-1) * x25) + x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th9341 t x03 x25 x35 x36 x56
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u2 u0)))))) h

theorem clause14758 (t x01 x05 x14 x25 x46 x56 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x05) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1)) ∨ (¬ (x67 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x01) + x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th9342 t x01 x05 x14 x25 x46 x56 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u9 (And.intro u4 (And.intro u5 (And.intro u8 (And.intro u3 (And.intro u1 (And.intro u6 u7))))))))))) h

theorem clause14759 (t x03 x12 x13 x23 x35 x37 x78 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ (¬ (x12 ≥ 0)) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
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
  have u3 : ((x03 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th9343 t x03 x12 x13 x23 x35 x37 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u7 (And.intro u1 (And.intro u6 (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u8 u3)))))))))) h

theorem clause14760 (t x02 x03 x13 x14 x24 x34 x35 x46 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + x14 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ ((t + ((-1) * x02)) ≤ 0)) := by
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
  have u3 : ((t + x14 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th9345 t x02 x03 x13 x14 x24 x34 x35 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u6 (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u9 (And.intro u4 (And.intro u3 (And.intro u8 u1))))))))))) h

theorem clause14761 (t x01 x04 x05 x07 x14 x46 x47 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((t + x47 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x05) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1)))) := by
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
  have u4 : ((x01 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 + ((-1) * x07)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x47 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x01) + x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th9347 t x01 x04 x05 x07 x14 x46 x47 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u7 (And.intro u4 (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u8 (And.intro u5 (And.intro u6 u9))))))))))) h

theorem clause14762 (t x03 x13 x34 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ ((t + ((-1) * x03) + x13) ≥ 1) ∨ (¬ (x13 ≥ 0)) ∨ ((t + ((-1) * x34)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x03) + x13) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th9348 t x03 x13 x34
  exact (fun hh => u1 (hh (And.intro u3 (And.intro u2 u0)))) h

theorem clause14763 (t x03 x13 x34 x35 x37 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ (x37 ≥ 0))) := by
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
  have u3 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x37 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9349 t x03 x13 x34 x35 x37
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u5 u6)))))))) h

theorem clause14764 (t x01 x03 x12 x13 x26 x35 x37 x67 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + ((-1) * x37) + x67) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x37) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th9351 t x01 x03 x12 x13 x26 x35 x37 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u6 (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u8 (And.intro u7 (And.intro u9 (And.intro u2 u5))))))))))) h

theorem clause14765 (t x01 x12 x26 x27 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x27)) ≥ 0)) ∨ (¬ (x67 ≥ 0)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x26 + ((-1) * x27)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th9352 t x01 x12 x26 x27 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u0 (And.intro u1 (And.intro u6 (And.intro u2 (And.intro u7 u5))))))))) h

theorem clause14766 (t x03 x14 x36 x37 x45 x47 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ ((t + ((-1) * x36)) ≤ 0) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x47)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x45 ≥ 0) := by
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
  have h := NineTheoryTrial.th9353 t x03 x14 x36 x37 x45 x47
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u4 (And.intro u6 (And.intro u3 (And.intro u1 (And.intro u5 (And.intro u0 u7)))))))) h

theorem clause14767 (t x01 x05 x12 x26 x57 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x05) ≥ 1)) ∨ (¬ ((t + x68 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x26 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x01) + x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x68 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th9354 t x01 x05 x12 x26 x57 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u4 (And.intro u6 (And.intro u3 (And.intro u1 (And.intro u7 u2))))))))) h

theorem clause14768 (t x01 x02 x04 x14 x25 x46 x47 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((t + x47 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x46)) ≥ 1) := by
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
  have u6 : ((x01 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x47 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th9356 t x01 x02 x04 x14 x25 x46 x47 x57
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u1 (And.intro u8 (And.intro u6 (And.intro u7 (And.intro u3 (And.intro u4 (And.intro u0 u2))))))))) h

theorem clause14769 (t x14 x23 x34 x37 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x14 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x47)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x14 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th9358 t x14 x23 x34 x37 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u5 u3))))))) h

theorem clause14770 (t x01 x03 x04 x12 x13 x23 x35 x37 x47 x67 x78 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x04)) ≥ 0)) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((t + ((-1) * x37) + x67) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
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
  have u3 : ((x03 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x37) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))))
  have u12 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))))
  have h := NineTheoryTrial.th9360 t x01 x03 x04 x12 x13 x23 x35 x37 x47 x67 x78
  exact (fun hh => (fun hh => hh u12) (hh (And.intro u6 (And.intro u9 (And.intro u11 (And.intro u8 (And.intro u0 (And.intro u7 (And.intro u2 (And.intro u10 (And.intro u5 (And.intro u4 (And.intro u3 u1))))))))))))) h

theorem clause14771 (t x03 x35 x36 x56 x58 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((t + ((-1) * x56) + x58) ≥ 1))) := by
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
  have u3 : ((x35 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x56) + x58) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th9361 t x03 x35 x36 x56 x58
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u5 u1)))))) h

theorem clause14772 (x23 x36 x37 : ℝ) : ((¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ ((x23 + ((-1) * x36)) ≤ (-1)) ∨ (¬ ((x36 + ((-1) * x37)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x36 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th9364 x23 x36 x37
  exact (fun hh => u1 (hh (And.intro u0 u2))) h

theorem clause14773 (t x13 x23 x25 x35 x36 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x23 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ ((t + ((-1) * x36)) ≤ 0) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x35 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th9365 t x13 x23 x25 x35 x36 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u6 (And.intro u1 (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u7 u5))))))))) h

theorem clause14774 (t x01 x02 x04 x25 x46 x58 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((t + ((-1) * x58) + x78) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
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
  have u5 : ((x01 + ((-1) * x04)) ≥ 0) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th9366 t x01 x02 x04 x25 x46 x58 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u7 (And.intro u4 (And.intro u2 (And.intro u6 (And.intro u3 (And.intro u0 (And.intro u1 u5)))))))))) h

theorem clause14775 (t x04 x07 x14 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x07)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x04) + x14) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x07 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x07)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x04) + x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th9370 t x04 x07 x14 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u3 u1))))))) h

theorem clause14776 (t x13 x23 x34 x35 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((t + ((-1) * x34) + x35) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
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
  have u3 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th9377 t x13 x23 x34 x35 x36
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u4 (And.intro u2 (And.intro u3 (And.intro u0 u1)))))) h

theorem clause14778 (x23 x25 x36 x56 : ℝ) : ((¬ ((x23 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x36 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ ((x25 + ((-1) * x56)) ≤ (-1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x23 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x36 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((x25 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th9381 x23 x25 x36 x56
  exact (fun hh => u3 (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause14779 (t x02 x05 x12 x14 x24 x25 x46 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x12) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1)))) := by
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
  have u4 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x57) + x67) ≥ 1) := by
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
  have h := NineTheoryTrial.th9385 t x02 x05 x12 x14 x24 x25 x46 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u7 (And.intro u4 (And.intro u6 u9))))))))))) h

theorem clause14780 (t x04 x12 x23 x24 x34 x37 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x34) + x37) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x34) + x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9386 t x04 x12 x23 x24 x34 x37
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u6 (And.intro u0 (And.intro u5 (And.intro u1 u4)))))))) h

theorem clause14781 (t x01 x12 x24 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ (x67 ≥ 0)) ∨ ((t + ((-1) * x01)) ≤ 0)) := by
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
  have u3 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th9389 t x01 x12 x24 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u4 (And.intro u2 (And.intro u5 (And.intro u0 (And.intro u3 u1)))))))) h

theorem clause14782 (t x03 x13 x34 x35 x37 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((t + ((-1) * x34) + x35) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1)))) := by
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
  have u3 : ((t + ((-1) * x34) + x35) ≥ 1) := by
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
  have h := NineTheoryTrial.th9394 t x03 x13 x34 x35 x37
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u0 u4)))))) h

theorem clause14783 (t x01 x03 x13 x14 x23 x35 x37 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + ((-1) * x37) + x67) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x37) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th9396 t x01 x03 x13 x14 x23 x35 x37 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u10 (And.intro u0 (And.intro u1 (And.intro u9 (And.intro u3 (And.intro u6 (And.intro u7 (And.intro u4 (And.intro u5 u8)))))))))))) h

theorem clause14784 (x14 x46 x47 : ℝ) : ((¬ ((x46 + ((-1) * x47)) ≥ 0)) ∨ ((x14 + ((-1) * x47)) ≥ 1) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x46 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th9400 x14 x46 x47
  exact (fun hh => u1 (hh (And.intro u0 u2))) h

theorem clause14785 (t x01 x07 x12 x17 x23 x24 x37 x47 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((t + x47 + ((-1) * x57)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x17 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x07 + ((-1) * x17)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x47 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x17 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x07 + ((-1) * x17)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th9402 t x01 x07 x12 x17 x23 x24 x37 x47 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u2 (And.intro u11 (And.intro u7 (And.intro u4 (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u9 (And.intro u10 (And.intro u3 u8))))))))))))) h

#print axioms clause14785
end NineCNFDirectTrial
