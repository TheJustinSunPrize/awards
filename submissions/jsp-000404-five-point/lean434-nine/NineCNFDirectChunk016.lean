import NineTheoryTrial

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineCNFDirectTrial

theorem clause15899 (t x12 x13 x23 x24 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((t + ((-1) * x23) + x24) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
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
  have u3 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th11740 t x12 x13 x23 x24 x36
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u2 (And.intro u5 (And.intro u3 (And.intro u1 u0)))))) h

theorem clause15900 (t x03 x04 x05 x12 x13 x24 x35 x36 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((t + x35 + ((-1) * x45)) ≥ 1)) ∨ ((t + ((-1) * x03)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x35 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x03)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th11741 t x03 x04 x05 x12 x13 x24 x35 x36 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u6 (And.intro u7 (And.intro u4 (And.intro u9 (And.intro u11 (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u10 (And.intro u8 u5))))))))))))) h

theorem clause15901 (t x02 x13 x26 x27 x35 x37 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ (x35 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x27 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1)) ∨ ((t + ((-1) * x26)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x26)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th11743 t x02 x13 x26 x27 x35 x37
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u3 (And.intro u4 (And.intro u1 (And.intro u0 (And.intro u6 (And.intro u2 u5))))))))) h

theorem clause15902 (t x01 x04 x16 x45 x58 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x04) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x58)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x58) + x78) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x01) + x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x16)) ≥ 1) := by
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
  have u6 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th11745 t x01 x04 x16 x45 x58 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u7 (And.intro u5 (And.intro u3 u6))))))))) h

theorem clause15903 (t x01 x03 x04 x13 x36 x37 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x04) ≥ 1)) ∨ (¬ ((t + x37 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x01) + x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x37 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th11746 t x01 x03 x04 x13 x36 x37 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u8 (And.intro u3 (And.intro u6 (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u5 u1)))))))))) h

theorem clause15904 (t x02 x03 x12 x23 x26 x35 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x02) + x12) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1)))) := by
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
  have u3 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x57) + x67) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th11751 t x02 x03 x12 x23 x26 x35 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u0 (And.intro u6 (And.intro u7 (And.intro u2 (And.intro u4 (And.intro u8 u1)))))))))) h

theorem clause15905 (t x03 x12 x23 x24 x34 x36 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((t + x34 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1))) := by
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
  have u3 : ((x24 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x34 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11754 t x03 x12 x23 x24 x34 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u6 (And.intro u2 (And.intro u1 u5)))))))) h

theorem clause15906 (t x02 x05 x07 x23 x24 x25 x47 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x23) + x25) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((t + x47 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x23) + x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x05 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x24)) ≥ 1) := by
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
  have u8 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th11756 t x02 x05 x07 x23 x24 x25 x47 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u9 (And.intro u4 (And.intro u2 (And.intro u7 (And.intro u0 (And.intro u6 (And.intro u5 (And.intro u8 u3))))))))))) h

theorem clause15907 (t x02 x04 x23 x24 x26 x34 x36 x45 x46 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x24 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((t + x67 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x45 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x67 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x26 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))))
  have u12 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))))
  have h := NineTheoryTrial.th11757 t x02 x04 x23 x24 x26 x34 x36 x45 x46 x67 x68
  exact (fun hh => (fun hh => hh u8) (hh (And.intro u3 (And.intro u7 (And.intro u11 (And.intro u2 (And.intro u4 (And.intro u9 (And.intro u0 (And.intro u1 (And.intro u12 (And.intro u5 (And.intro u6 u10))))))))))))) h

theorem clause15908 (t x02 x24 x26 x34 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((t + x45 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x45 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11759 t x02 x24 x26 x34 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u2 (And.intro u3 u0)))))))) h

theorem clause15909 (t x01 x05 x13 x36 x45 x56 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x05) ≥ 1)) ∨ (¬ (x67 ≥ 0))) := by
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
  have u3 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x67)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x01) + x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th11762 t x01 x05 x13 x36 x45 x56 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u6 (And.intro u7 (And.intro u8 (And.intro u1 (And.intro u5 (And.intro u2 u9))))))))))) h

theorem clause15910 (t x01 x05 x13 x36 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + x67 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x05) ≥ 1))) := by
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
  have u3 : ((t + x67 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x01) + x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th11766 t x01 x05 x13 x36 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u2 (And.intro u6 (And.intro u4 (And.intro u1 (And.intro u0 u7))))))))) h

theorem clause15911 (t x26 x36 x45 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x68)) ≤ (-1))) ∨ (¬ (x67 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th11768 t x26 x36 x45 x56 x67 x68
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u3 (And.intro u5 (And.intro u4 (And.intro u6 (And.intro u7 (And.intro u2 u0)))))))) h

theorem clause15912 (t x02 x04 x07 x23 x24 x25 x35 x47 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + ((-1) * x47) + x57) ≥ 1)) ∨ (¬ ((t + ((-1) * x23) + x24) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x47) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x23) + x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x04 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x04 + ((-1) * x07)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th11771 t x02 x04 x07 x23 x24 x25 x35 x47 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u9 (And.intro u7 (And.intro u5 (And.intro u10 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u6 (And.intro u4 u2)))))))))))) h

theorem clause15913 (t x02 x04 x23 x24 x25 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x23) + x24) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x23) + x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x56) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th11773 t x02 x04 x23 x24 x25 x45 x56 x57
  exact (fun hh => (fun hh => hh u8) (hh (And.intro u4 (And.intro u6 (And.intro u3 (And.intro u7 (And.intro u1 (And.intro u5 (And.intro u2 u0))))))))) h

theorem clause15914 (t x03 x04 x23 x34 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x03) + x23) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1))) := by
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
  have u3 : ((t + ((-1) * x03) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th11775 t x03 x04 x23 x34 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u5 u2))))))) h

theorem clause15915 (t x01 x02 x12 x15 x17 x23 x36 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x15) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x57)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≤ 0) := by
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
  have u4 : ((t + ((-1) * x57) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x12) + x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x17 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th11776 t x01 x02 x12 x15 x17 x23 x36 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u9 (And.intro u0 (And.intro u8 (And.intro u7 (And.intro u4 (And.intro u5 (And.intro u3 (And.intro u1 u6))))))))))) h

theorem clause15916 (t x02 x24 x34 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ (x45 ≥ 0))) := by
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
  have u3 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11778 t x02 x24 x34 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u6 (And.intro u0 (And.intro u2 u3)))))))) h

theorem clause15917 (x34 x45 x46 : ℝ) : (((x34 + ((-1) * x45)) ≥ 1) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x46)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th11780 x34 x45 x46
  exact (fun hh => u0 (hh (And.intro u2 u1))) h

theorem clause15918 (x02 x05 x26 x56 : ℝ) : ((¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x05)) ≥ 0)) ∨ ((x02 + ((-1) * x26)) ≥ 1) ∨ (¬ ((x26 + ((-1) * x56)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x02 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x26 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th11781 x02 x05 x26 x56
  exact (fun hh => u2 (hh (And.intro u0 (And.intro u1 u3)))) h

theorem clause15920 (t x01 x15 x25 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ (x57 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
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
  have u4 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x57 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11785 t x01 x15 x25 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u5 (And.intro u0 (And.intro u4 (And.intro u6 u1)))))))) h

theorem clause15921 (t x01 x03 x13 x15 x23 x25 x34 x35 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((t + x25 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1))) ∨ ((t + ((-1) * x01)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
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
  have u4 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x25 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
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
  have u9 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th11786 t x01 x03 x13 x15 x23 x25 x34 x35 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u4 (And.intro u10 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u7 (And.intro u5 (And.intro u6 (And.intro u2 u9)))))))))))) h

theorem clause15922 (x15 x25 x56 : ℝ) : ((¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ ((x15 + ((-1) * x56)) ≤ (-1)) ∨ (¬ ((x15 + ((-1) * x25)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x15 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th11788 x15 x25 x56
  exact (fun hh => u1 (hh (And.intro u0 u2))) h

theorem clause15923 (t x01 x05 x12 x13 x15 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x15)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x05)) ≥ 0) := by
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
  have u4 : ((x12 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11789 t x01 x05 x12 x13 x15 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 (And.intro u6 u1)))))))) h

theorem clause15924 (t x01 x03 x12 x13 x36 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + x12 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th11790 t x01 x03 x12 x13 x36
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u2 (And.intro u5 (And.intro u1 (And.intro u3 u4)))))) h

theorem clause15926 (t x01 x12 x13 x15 x25 x36 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1)))) := by
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
  have u3 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x57) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th11796 t x01 x12 x13 x15 x25 x36 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u8 (And.intro u2 (And.intro u7 (And.intro u0 (And.intro u6 (And.intro u1 (And.intro u4 u3)))))))))) h

theorem clause15927 (t x01 x02 x12 x13 x16 x24 x36 x47 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((t + ((-1) * x47) + x67) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x36)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x12 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x47) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x16 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th11797 t x01 x02 x12 x13 x16 x24 x36 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u6 (And.intro u1 (And.intro u8 (And.intro u2 (And.intro u9 (And.intro u7 (And.intro u5 u4))))))))))) h

theorem clause15928 (t x01 x02 x04 x12 x13 x16 x24 x36 x45 x47 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x67 ≥ 0)) ∨ (¬ ((x16 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
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
  have u4 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x16 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))))
  have u12 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))))
  have h := NineTheoryTrial.th11798 t x01 x02 x04 x12 x13 x16 x24 x36 x45 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u4 (And.intro u2 (And.intro u9 (And.intro u10 (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u12 (And.intro u8 (And.intro u11 (And.intro u6 u3)))))))))))))) h

theorem clause15929 (t x02 x03 x12 x13 x24 x36 x45 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1)))) := by
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
  have u3 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x57) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th11799 t x02 x03 x12 x13 x24 x36 x45 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u6 (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u2 (And.intro u5 (And.intro u8 (And.intro u1 u9))))))))))) h

theorem clause15930 (t x01 x02 x12 x13 x17 x24 x45 x56 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
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
  have u5 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th11800 t x01 x02 x12 x13 x17 x24 x45 x56 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u6 (And.intro u7 (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u2 (And.intro u9 (And.intro u8 u10)))))))))))) h

theorem clause15931 (t x04 x14 x25 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x14)) ≥ 0)) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1)) ∨ (¬ (x14 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x14 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th11802 t x04 x14 x25 x45 x56 x57
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u3 (And.intro u4 (And.intro u6 (And.intro u2 (And.intro u0 (And.intro u7 u1)))))))) h

theorem clause15933 (t x01 x02 x05 x12 x13 x16 x25 x56 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x05)) ≤ 0)) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1)) ∨ (¬ (x67 ≥ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
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
  have u5 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th11806 t x01 x02 x05 x12 x13 x16 x25 x56 x57 x67
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u5 (And.intro u8 (And.intro u9 (And.intro u11 (And.intro u2 (And.intro u10 (And.intro u3 (And.intro u0 (And.intro u7 (And.intro u4 u1)))))))))))) h

theorem clause15934 (t x02 x03 x04 x05 x06 x25 x36 x56 x57 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x02 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x05)) ≤ 0)) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x06)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1)) ∨ (¬ (x67 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x02 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x06 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
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
  have u11 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))))
  have u12 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))))
  have h := NineTheoryTrial.th11807 t x02 x03 x04 x05 x06 x25 x36 x56 x57 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u10 (And.intro u7 (And.intro u11 (And.intro u8 (And.intro u4 (And.intro u2 (And.intro u9 (And.intro u1 (And.intro u5 (And.intro u6 u12)))))))))))))) h

theorem clause15935 (t x02 x03 x12 x13 x24 x36 x47 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + x68 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
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
  have u5 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x68 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th11808 t x02 x03 x12 x13 x24 x36 x47 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u2 (And.intro u9 (And.intro u7 (And.intro u0 (And.intro u1 (And.intro u8 (And.intro u4 u6))))))))))) h

theorem clause15936 (t x05 x25 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x05 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x05 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th11809 t x05 x25 x45 x56 x57
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 (And.intro u0 (And.intro u4 (And.intro u3 u5)))))) h

theorem clause15937 (t x02 x03 x04 x12 x13 x24 x36 x45 x47 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x47) + x67) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
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
  have u6 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x47) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th11810 t x02 x03 x04 x12 x13 x24 x36 x45 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u9 (And.intro u8 (And.intro u0 (And.intro u3 (And.intro u10 (And.intro u4 (And.intro u2 (And.intro u1 (And.intro u6 (And.intro u7 u5)))))))))))) h

theorem clause15938 (t x01 x02 x12 x13 x16 x25 x36 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x36)) ≥ 0))) := by
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
  have u5 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x57) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x16 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th11811 t x01 x02 x12 x13 x16 x25 x36 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u4 (And.intro u7 (And.intro u8 (And.intro u5 (And.intro u6 (And.intro u9 (And.intro u0 u3))))))))))) h

theorem clause15939 (t x04 x07 x24 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x04 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x04 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x07)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th11813 t x04 x07 x24 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u5 (And.intro u3 (And.intro u0 u1))))))) h

theorem clause15940 (t x01 x14 x16 x24 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((t + x14 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x46)) ≥ 1) := by
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
  have u4 : ((x16 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th11816 t x01 x14 x16 x24 x46
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u2 u3)))))) h

theorem clause15941 (t x02 x04 x06 x24 x36 x45 x46 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + x36 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((t + x02 + ((-1) * x06)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x36 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x06 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x02 + ((-1) * x06)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th11817 t x02 x04 x06 x24 x36 x45 x46 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u1 (And.intro u8 (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u5 (And.intro u6 u2)))))))))) h

theorem clause15942 (t x02 x03 x04 x25 x36 x45 x57 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x02 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x25 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + x68 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x02 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x25 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x68 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th11818 t x02 x03 x04 x25 x36 x45 x57 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u1 (And.intro u0 (And.intro u5 (And.intro u3 (And.intro u6 (And.intro u2 (And.intro u9 (And.intro u4 u8))))))))))) h

theorem clause15943 (t x01 x02 x12 x13 x17 x27 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + x17 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1)))) := by
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
  have u4 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x17 + ((-1) * x57)) ≥ 1) := by
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
  have h := NineTheoryTrial.th11819 t x01 x02 x12 x13 x17 x27 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u8 (And.intro u7 (And.intro u0 (And.intro u4 (And.intro u5 (And.intro u6 u1)))))))))) h

theorem clause15945 (t x25 x56 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1)) ∨ (¬ (x67 ≥ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 + ((-1) * x57)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11821 t x25 x56 x57 x67 x78
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u2 (And.intro u4 (And.intro u3 (And.intro u5 (And.intro u0 u1))))))) h

theorem clause15946 (t x03 x35 x36 x56 x57 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1))) := by
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
  have u3 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x56) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th11828 t x03 x35 x36 x56 x57
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u0 u5)))))) h

theorem clause15947 (t x02 x03 x24 x35 x45 x56 x57 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((t + x02 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1))) := by
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
  have u4 : ((t + x02 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x56) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th11829 t x02 x03 x24 x35 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u2 (And.intro u7 (And.intro u6 (And.intro u3 u5))))))))) h

theorem clause15948 (t x01 x05 x12 x14 x15 x47 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((t + ((-1) * x47) + x67) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + x12 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x15)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x47) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x12 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x05 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th11831 t x01 x05 x12 x14 x15 x47 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u7 (And.intro u1 (And.intro u2 (And.intro u5 (And.intro u0 (And.intro u8 u6)))))))))) h

theorem clause15949 (t x01 x05 x06 x12 x13 x15 x36 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + ((-1) * x36) + x56) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x06)) ≥ 0)) ∨ (¬ ((t + x12 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x15)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
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
  have u3 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x36) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x12 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x05 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th11832 t x01 x05 x06 x12 x13 x15 x36 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u9 (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u5 (And.intro u3 (And.intro u4 (And.intro u6 u7))))))))))) h

theorem clause15950 (t x01 x12 x15 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
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
  have h := NineTheoryTrial.th11833 t x01 x12 x15 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u4 (And.intro u3 u2)))))))) h

theorem clause15951 (t x02 x03 x04 x24 x36 x45 x48 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x02 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x78 ≥ 0)) ∨ (¬ ((x04 + ((-1) * x48)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x48)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x02 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x67)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x04 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x24 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th11834 t x02 x03 x04 x24 x36 x45 x48 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u7 (And.intro u6 (And.intro u8 (And.intro u3 (And.intro u10 (And.intro u1 (And.intro u2 (And.intro u9 u5)))))))))))) h

theorem clause15952 (t x01 x03 x12 x13 x16 x36 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x16) + x56) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
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
  have u4 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x16) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th11836 t x01 x03 x12 x13 x16 x36 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u0 (And.intro u6 (And.intro u7 (And.intro u3 (And.intro u1 (And.intro u5 u8)))))))))) h

theorem clause15953 (t x01 x03 x12 x13 x14 x35 x36 x47 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x47) + x67) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ ((t + ((-1) * x35)) ≤ 0) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x47) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th11837 t x01 x03 x12 x13 x14 x35 x36 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u6 (And.intro u3 (And.intro u0 (And.intro u10 (And.intro u8 (And.intro u4 (And.intro u7 (And.intro u1 (And.intro u5 u9)))))))))))) h

theorem clause15954 (t x01 x03 x05 x12 x13 x17 x35 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x17) + x57) ≥ 1))) := by
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
  have u6 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x03 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x17) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th11838 t x01 x03 x05 x12 x13 x17 x35 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u3 (And.intro u4 (And.intro u0 (And.intro u9 (And.intro u1 (And.intro u6 (And.intro u2 (And.intro u5 u7))))))))))) h

theorem clause15955 (t x01 x03 x12 x13 x17 x27 x35 x56 x67 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + ((-1) * x27) + x67) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x27)) ≤ 0))) := by
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
  have u3 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x27) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x17 + ((-1) * x27)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th11839 t x01 x03 x12 x13 x17 x27 x35 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u5 (And.intro u0 (And.intro u7 (And.intro u9 (And.intro u6 u4))))))))))) h

theorem clause15957 (t x17 x27 x67 : ℝ) : ((¬ ((t + ((-1) * x27) + x67) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x27)) ≤ 0)) ∨ ((t + ((-1) * x17) + x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x27) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x17 + ((-1) * x27)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x17) + x67) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th11841 t x17 x27 x67
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause15958 (t x01 x12 x16 x17 x36 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x17) + x67) ≥ 1)) ∨ (¬ ((t + x12 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x67)) ≥ 1) := by
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
  have u6 : ((t + x12 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x16 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th11842 t x01 x12 x16 x17 x36 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u6 (And.intro u7 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u4 u2))))))))) h

theorem clause15959 (t x01 x03 x05 x12 x13 x17 x27 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((t + ((-1) * x27) + x67) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x27)) ≤ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
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
  have u5 : ((t + ((-1) * x27) + x67) ≥ 1) := by
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
  have u8 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x17 + ((-1) * x27)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th11846 t x01 x03 x05 x12 x13 x17 x27 x57 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u8 (And.intro u5 (And.intro u9 (And.intro u4 (And.intro u6 (And.intro u7 u10)))))))))))) h

theorem clause15960 (t x01 x03 x05 x12 x13 x18 x36 x56 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x36 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((t + ((-1) * x18) + x78) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x18)) ≤ (-1)))) := by
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
  have u5 : ((x36 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x18) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x01 + ((-1) * x18)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th11847 t x01 x03 x05 x12 x13 x18 x36 x56 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u9 (And.intro u4 (And.intro u7 (And.intro u10 (And.intro u8 (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u2 u3)))))))))))) h

theorem clause15961 (t x01 x05 x13 x18 x35 x36 x56 x58 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x13)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((t + ((-1) * x05) + x35) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x78 ≥ 0)) ∨ (¬ ((x18 + ((-1) * x58)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x18)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x05) + x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x18 + ((-1) * x58)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x01 + ((-1) * x18)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th11848 t x01 x05 x13 x18 x35 x36 x56 x58 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u6 (And.intro u2 (And.intro u10 (And.intro u4 (And.intro u8 (And.intro u7 (And.intro u9 (And.intro u11 u3))))))))))))) h

theorem clause15962 (t x02 x05 x12 x15 x24 x35 x48 x57 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x35 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((t + ((-1) * x48) + x58) ≥ 1)) ∨ (¬ ((t + x12 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x15)) ≤ 0)) ∨ (¬ ((x24 + ((-1) * x48)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x48) + x58) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x12 + ((-1) * x15)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x05 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x24 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th11849 t x02 x05 x12 x15 x24 x35 x48 x57 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u4 (And.intro u5 (And.intro u0 (And.intro u3 (And.intro u7 (And.intro u8 (And.intro u9 u6))))))))))) h

theorem clause15963 (t x01 x03 x12 x13 x15 x36 x56 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
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
  have u4 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x67)) ≥ 1) := by
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
  have h := NineTheoryTrial.th11851 t x01 x03 x12 x13 x15 x36 x56 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u4 (And.intro u0 (And.intro u2 (And.intro u8 (And.intro u5 (And.intro u9 (And.intro u7 (And.intro u10 (And.intro u3 u1)))))))))))) h

theorem clause15964 (x16 x36 x67 : ℝ) : ((¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x36)) ≥ 0)) ∨ ((x16 + ((-1) * x67)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x16 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x16 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th11854 x16 x36 x67
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause15965 (t x01 x02 x12 x13 x15 x25 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
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
  have u5 : ((t + ((-1) * x56) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th11855 t x01 x02 x12 x13 x15 x25 x56 x57
  exact (fun hh => (fun hh => hh u7) (hh (And.intro u3 (And.intro u5 (And.intro u0 (And.intro u1 (And.intro u6 (And.intro u8 (And.intro u2 u4))))))))) h

theorem clause15966 (t x01 x13 x16 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x13)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x56 ≥ 0) := by
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
  have h := NineTheoryTrial.th11856 t x01 x13 x16 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u5 (And.intro u0 (And.intro u4 (And.intro u3 u6)))))))) h

theorem clause15967 (t x01 x13 x15 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x13)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ (x67 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11858 t x01 x13 x15 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u0 (And.intro u2 (And.intro u6 (And.intro u4 u3)))))))) h

theorem clause15969 (t x01 x15 x16 x24 x45 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x24)) ≤ 0) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ (x67 ≥ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x16)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th11862 t x01 x15 x16 x24 x45 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u7 (And.intro u6 (And.intro u5 u4))))))))) h

theorem clause15970 (t x02 x03 x05 x24 x35 x47 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + ((-1) * x47) + x57) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((t + x02 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x05)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
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
  have u5 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x02 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x03 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th11869 t x02 x03 x05 x24 x35 x47 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u6 (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u8 (And.intro u7 (And.intro u4 u3)))))))))) h

theorem clause15971 (t x02 x03 x24 x35 x47 x56 x67 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((t + x02 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((t + ((-1) * x47) + x67) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1))) := by
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
  have u3 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x02 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x47) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th11870 t x02 x03 x24 x35 x47 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u4 (And.intro u1 (And.intro u5 (And.intro u0 (And.intro u7 (And.intro u3 u6))))))))) h

theorem clause15972 (t x02 x03 x04 x05 x24 x35 x45 x47 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + x02 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x05)) ≥ 0)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ (x57 ≥ 0)) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
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
  have u3 : ((t + x02 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x03 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : (x57 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th11871 t x02 x03 x04 x05 x24 x35 x45 x47 x56 x57
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u9 (And.intro u8 (And.intro u5 (And.intro u6 (And.intro u7 (And.intro u3 (And.intro u11 (And.intro u2 (And.intro u0 (And.intro u1 u10)))))))))))) h

theorem clause15973 (t x01 x04 x12 x13 x14 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x12 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x14)) ≤ 0))) := by
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
  have u3 : ((x04 + ((-1) * x47)) ≥ 1) := by
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
  have u6 : ((x12 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11873 t x01 x04 x12 x13 x14 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u6 (And.intro u4 u1)))))))) h

theorem clause15975 (t x01 x14 x15 x34 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x14) + x34) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x14) + x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th11875 t x01 x14 x15 x34 x45
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u1 u4)))))) h

theorem clause15976 (t x01 x02 x13 x25 x35 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1)))) := by
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
  have u5 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x56) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th11877 t x01 x02 x13 x25 x35 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u3 (And.intro u5 (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u1 u6))))))))) h

theorem clause15977 (t x13 x24 x34 x36 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + ((-1) * x24) + x34) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x24) + x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th11880 t x13 x24 x34 x36 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u3 (And.intro u1 (And.intro u0 u2))))))) h

theorem clause15978 (t x01 x02 x03 x13 x25 x36 x37 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + x37 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x37 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th11881 t x01 x02 x03 x13 x25 x36 x37 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u3 (And.intro u6 (And.intro u0 (And.intro u7 (And.intro u8 (And.intro u2 u5)))))))))) h

theorem clause15979 (t x01 x02 x16 x24 x45 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
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
  have u4 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x57) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th11885 t x01 x02 x16 x24 x45 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u3 (And.intro u5 (And.intro u0 (And.intro u7 (And.intro u6 (And.intro u2 u1))))))))) h

theorem clause15980 (t x01 x02 x16 x24 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
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
  have u3 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x46) + x56) ≥ 1) := by
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
  have h := NineTheoryTrial.th11886 t x01 x02 x16 x24 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u6 (And.intro u7 (And.intro u0 (And.intro u3 (And.intro u2 u1))))))))) h

theorem clause15981 (t x01 x02 x13 x25 x35 x37 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((t + x35 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x37)) ≤ 0))) := by
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
  have u3 : ((t + x35 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x35 + ((-1) * x37)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th11888 t x01 x02 x13 x25 x35 x37 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u7 (And.intro u5 (And.intro u3 (And.intro u4 (And.intro u6 u8)))))))))) h

theorem clause15982 (t x06 x13 x16 x34 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + x34 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x16)) ≤ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x34 + ((-1) * x36)) ≥ 1) := by
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
  have u5 : ((x13 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11889 t x06 x13 x16 x34 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u1 (And.intro u3 (And.intro u6 (And.intro u4 u5)))))))) h

theorem clause15983 (t x01 x05 x13 x23 x25 x34 x36 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((t + x34 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x05) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
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
  have u3 : ((x23 + ((-1) * x25)) ≥ 0) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th11890 t x01 x05 x13 x23 x25 x34 x36 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u5 (And.intro u6 (And.intro u0 (And.intro u2 (And.intro u4 (And.intro u1 (And.intro u3 u8)))))))))) h

theorem clause15984 (t x04 x23 x24 x34 x36 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + x34 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x34)) ≥ 0) := by
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
  have u5 : ((t + x34 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11891 t x04 x23 x24 x34 x36 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u0 (And.intro u4 (And.intro u5 (And.intro u1 (And.intro u2 u3)))))))) h

theorem clause15985 (t x01 x02 x06 x13 x16 x24 x34 x45 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x06)) ≥ 0)) ∨ (¬ (x34 ≥ 0)) ∨ (¬ ((x13 + ((-1) * x16)) ≤ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1)))) := by
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
  have u3 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x13 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th11892 t x01 x02 x06 x13 x16 x24 x34 x45 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u9 (And.intro u3 (And.intro u0 (And.intro u6 (And.intro u10 (And.intro u11 (And.intro u7 (And.intro u2 (And.intro u4 (And.intro u5 (And.intro u8 u1))))))))))))) h

theorem clause15987 (t x04 x24 x45 x47 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ (x04 ≥ 0)) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x04 ≥ 0) := by
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
  have h := NineTheoryTrial.th11896 t x04 x24 x45 x47 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u3 (And.intro u1 (And.intro u0 (And.intro u2 u6)))))))) h

theorem clause15988 (t x13 x16 x23 x34 x36 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ (x34 ≥ 0)) ∨ (¬ ((x13 + ((-1) * x16)) ≤ 0)) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x68)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x16 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th11897 t x13 x16 x23 x34 x36 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u6 (And.intro u2 (And.intro u7 (And.intro u1 (And.intro u5 u4))))))))) h

theorem clause15989 (t x01 x04 x16 x45 x57 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x04) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + x68 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x01) + x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x68 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x16 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th11900 t x01 x04 x16 x45 x57 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u7 (And.intro u3 (And.intro u1 (And.intro u6 (And.intro u4 u5))))))))) h

theorem clause15990 (t x03 x24 x35 x37 x46 x47 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ (x35 ≥ 0)) ∨ ((t + ((-1) * x46)) ≤ 0) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x47)) ≤ 0)) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
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
  have h := NineTheoryTrial.th11902 t x03 x24 x35 x37 x46 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u6 (And.intro u4 (And.intro u7 (And.intro u1 (And.intro u0 u3))))))))) h

theorem clause15991 (t x01 x04 x13 x24 x37 x45 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x04) ≥ 1)) ∨ (¬ ((t + x37 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≥ 1) := by
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
  have u5 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x01) + x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x37 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th11903 t x01 x04 x13 x24 x37 x45 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u0 (And.intro u6 (And.intro u1 (And.intro u3 (And.intro u4 u7))))))))) h

theorem clause15992 (x24 x45 x46 : ℝ) : (((x24 + ((-1) * x45)) ≤ (-1)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x46)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th11907 x24 x45 x46
  exact (fun hh => u0 (hh (And.intro u2 u1))) h

theorem clause15993 (t x01 x02 x15 x24 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
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
  have u4 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th11913 t x01 x02 x15 x24 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u7 (And.intro u6 (And.intro u5 u1))))))))) h

theorem clause15994 (t x24 x45 x47 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x57)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x56) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th11917 t x24 x45 x47 x56 x57
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u4 u3)))))) h

theorem clause15995 (t x01 x04 x15 x24 x45 x47 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x04) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ (x67 ≥ 0)) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x01) + x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th11920 t x01 x04 x15 x24 x45 x47 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u6 (And.intro u5 (And.intro u7 (And.intro u3 (And.intro u8 (And.intro u9 (And.intro u1 u4))))))))))) h

theorem clause15996 (t x01 x02 x15 x24 x47 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x47) + x67) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
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
  have u4 : ((t + ((-1) * x47) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x67)) ≥ 1) := by
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
  have h := NineTheoryTrial.th11921 t x01 x02 x15 x24 x47 x56 x67
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u5 (And.intro u7 (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u6 u0)))))))) h

theorem clause15997 (t x01 x04 x16 x24 x45 x47 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x47) + x67) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x04) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x47) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x01) + x04) ≥ 1) := by
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
  have h := NineTheoryTrial.th11929 t x01 x04 x16 x24 x45 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u5 (And.intro u4 u6))))))))) h

theorem clause15998 (t x24 x37 x46 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x46)) ≤ 0) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1))) ∨ (¬ (x37 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x47)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x37 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11930 t x24 x37 x46 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u6 u0)))))))) h

theorem clause16000 (t x05 x13 x15 x25 x34 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x25)) ≤ 0)) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ (x34 ≥ 0)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x15)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th11933 t x05 x13 x15 x25 x34 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u8 (And.intro u4 (And.intro u7 u6)))))))))) h

theorem clause16001 (t x15 x24 x45 x48 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + x15 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x48 + ((-1) * x58)) ≥ 0)) ∨ (¬ ((x15 + ((-1) * x58)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x48)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x15 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x48 + ((-1) * x58)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th11936 t x15 x24 x45 x48 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u1 u5))))))) h

theorem clause16002 (t x01 x04 x13 x36 x46 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + x67 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x04) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x67 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x01) + x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th11941 t x01 x04 x13 x36 x46 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u7 (And.intro u4 (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u6 u5))))))))) h

theorem clause16003 (t x02 x03 x06 x12 x23 x24 x25 x36 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ ((x02 + ((-1) * x12)) ≤ 0) ∨ (¬ ((t + ((-1) * x23) + x24) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x23)) ≤ 0)) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x06)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x67 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
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
  have u5 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x03 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x06 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))))
  have u12 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))))
  have h := NineTheoryTrial.th11943 t x02 x03 x06 x12 x23 x24 x25 x36 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u3 (And.intro u8 (And.intro u10 (And.intro u9 (And.intro u2 (And.intro u6 (And.intro u12 (And.intro u11 (And.intro u7 u4)))))))))))))) h

theorem clause16004 (t x03 x05 x12 x15 x23 x24 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + ((-1) * x23) + x24) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x15)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x23) + x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th11949 t x03 x05 x12 x15 x23 x24 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u6 (And.intro u3 (And.intro u4 (And.intro u1 (And.intro u7 u5))))))))) h

theorem clause16005 (t x01 x15 x35 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ (x57 ≥ 0))) := by
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
  have u3 : ((x15 + ((-1) * x56)) ≥ 1) := by
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
  have h := NineTheoryTrial.th11950 t x01 x15 x35 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u6 (And.intro u2 (And.intro u5 (And.intro u4 (And.intro u3 u0)))))))) h

theorem clause16007 (t x02 x05 x06 x12 x24 x25 x46 x56 x57 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ (x24 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ ((t + ((-1) * x46)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x56) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x06 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x05 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th11954 t x02 x05 x06 x12 x24 x25 x46 x56 x57 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u7 (And.intro u9 (And.intro u5 (And.intro u8 (And.intro u3 (And.intro u10 (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u6 u11))))))))))))) h

theorem clause16008 (t x02 x12 x13 x23 x25 x34 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th11956 t x02 x12 x13 x23 x25 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u7 (And.intro u5 (And.intro u6 (And.intro u4 (And.intro u1 u3))))))))) h

theorem clause16009 (t x01 x03 x13 x35 x36 x67 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x67 ≥ 0)) ∨ ((t + ((-1) * x01)) ≤ 0)) := by
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
  have u5 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th11957 t x01 x03 x13 x35 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u7 (And.intro u3 (And.intro u6 (And.intro u2 (And.intro u0 (And.intro u5 u4))))))))) h

theorem clause16010 (t x05 x06 x13 x16 x34 x35 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + x34 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x06)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x16)) ≤ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x34 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x06)) ≥ 0) := by
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
  have h := NineTheoryTrial.th11958 t x05 x06 x13 x16 x34 x35 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u7 (And.intro u2 (And.intro u6 (And.intro u5 (And.intro u0 (And.intro u1 u3))))))))) h

theorem clause16011 (t x01 x12 x25 x26 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0)) := by
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
  have u5 : ((x25 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th11960 t x01 x12 x25 x26 x56 x67
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u3 (And.intro u7 (And.intro u0 (And.intro u6 (And.intro u2 (And.intro u5 u1)))))))) h

theorem clause16012 (t x02 x04 x12 x15 x16 x24 x25 x46 x47 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x12) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x47)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x16)) ≥ 0)) ∨ (¬ ((x15 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x02) + x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x46) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x15 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x15 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th11961 t x02 x04 x12 x15 x16 x24 x25 x46 x47 x56 x67
  exact (fun hh => (fun hh => hh u7) (hh (And.intro u11 (And.intro u8 (And.intro u9 (And.intro u1 (And.intro u3 (And.intro u6 (And.intro u0 (And.intro u10 (And.intro u5 (And.intro u4 u2)))))))))))) h

theorem clause16013 (t x06 x15 x56 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((t + ((-1) * x06) + x56) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x57 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x06) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th11962 t x06 x15 x56 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u2 u5))))))) h

theorem clause16014 (t x02 x04 x12 x24 x25 x47 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x12) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((t + ((-1) * x47) + x67) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1)))) := by
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
  have u3 : ((x04 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x47) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th11963 t x02 x04 x12 x24 x25 x47 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u5 (And.intro u3 (And.intro u6 (And.intro u8 (And.intro u4 u7)))))))))) h

theorem clause16015 (t x02 x04 x25 x34 x35 x45 x47 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x35 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ (x34 ≥ 0)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x35 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th11964 t x02 x04 x25 x34 x35 x45 x47 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u1 (And.intro u3 (And.intro u5 (And.intro u6 (And.intro u0 (And.intro u7 (And.intro u4 (And.intro u9 u2))))))))))) h

theorem clause16016 (t x02 x03 x12 x24 x26 x36 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x03)) ≤ 0) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x26) + x56) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x03)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x36)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x26) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th11970 t x02 x03 x12 x24 x26 x36 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u9 (And.intro u7 (And.intro u6 (And.intro u5 (And.intro u4 (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u8 u3))))))))))) h

theorem clause16017 (t x06 x13 x25 x35 x36 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((t + ((-1) * x25) + x35) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x25) + x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11972 t x06 x13 x25 x35 x36 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u4 (And.intro u2 (And.intro u6 (And.intro u3 u0)))))))) h

theorem clause16018 (t x01 x03 x07 x13 x36 x37 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((t + x37 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x07) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x37 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x01) + x07) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th11977 t x01 x03 x07 x13 x36 x37 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u7 (And.intro u0 (And.intro u6 (And.intro u8 (And.intro u2 (And.intro u5 u3)))))))))) h

theorem clause16019 (t x01 x02 x12 x15 x24 x27 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((t + ((-1) * x27) + x67) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1)))) := by
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
  have u3 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x27) + x67) ≥ 1) := by
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
  have u8 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x02 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th11978 t x01 x02 x12 x15 x24 x27 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u8 (And.intro u2 (And.intro u9 (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u6 (And.intro u7 u5))))))))))) h

theorem clause16020 (t x02 x13 x26 x27 x34 x37 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ (x34 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x27 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1)) ∨ ((t + ((-1) * x26)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x26)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th11979 t x02 x13 x26 x27 x34 x37
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u4 (And.intro u5 (And.intro u6 u2))))))))) h

theorem clause16021 (t x03 x04 x12 x15 x24 x35 x47 x56 x68 x78 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ ((t + ((-1) * x03)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x15 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((t + x68 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x03)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x24)) ≥ 0) := by
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
  have u6 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x15 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((t + x68 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th11980 t x03 x04 x12 x15 x24 x35 x47 x56 x68 x78
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u5 (And.intro u9 (And.intro u1 (And.intro u2 (And.intro u6 (And.intro u11 (And.intro u8 (And.intro u3 (And.intro u0 (And.intro u7 u10)))))))))))) h

theorem clause16022 (t x02 x12 x24 x26 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ ((t + ((-1) * x68)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x68)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
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
  have u6 : ((x26 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th11982 t x02 x12 x24 x26 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u5 (And.intro u4 (And.intro u6 u3)))))))) h

theorem clause16023 (t x01 x07 x13 x36 x47 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + ((-1) * x47) + x67) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x07) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
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
  have u3 : ((t + ((-1) * x47) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x01) + x07) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th11983 t x01 x07 x13 x36 x47 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u6 (And.intro u1 (And.intro u2 (And.intro u3 (And.intro u5 (And.intro u0 u7))))))))) h

theorem clause16024 (t x01 x02 x12 x13 x24 x27 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((t + ((-1) * x27) + x67) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1)))) := by
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
  have u3 : ((x02 + ((-1) * x24)) ≥ 1) := by
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
  have u6 : ((t + ((-1) * x27) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x02 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th11984 t x01 x02 x12 x13 x24 x27 x36 x67
  exact (fun hh => (fun hh => hh u9) (hh (And.intro u8 (And.intro u1 (And.intro u7 (And.intro u2 (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u6 u5)))))))))) h

theorem clause16025 (t x05 x36 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ ((t + ((-1) * x05)) ≤ 0) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x67 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x05)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 + ((-1) * x68)) ≥ 1) := by
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
  have h := NineTheoryTrial.th11985 t x05 x36 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u3 u6)))))))) h

theorem clause16026 (t x35 x45 x46 x56 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x35 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1)))) := by
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
  have u3 : ((x45 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th11987 t x35 x45 x46 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u3 (And.intro u4 u1))))))) h

theorem clause16027 (t x24 x27 x45 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x45) + x47) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x27)) ≥ 0)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x45) + x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x27)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th11989 t x24 x27 x45 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u4 (And.intro u2 u5))))))) h

theorem clause16028 (t x24 x27 x34 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x24) + x34) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x27)) ≥ 0)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x24) + x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x27)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th11990 t x24 x27 x34 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u5 (And.intro u0 (And.intro u3 u2))))))) h

theorem clause16029 (t x01 x02 x03 x27 x35 x56 x68 x78 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((t + x68 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1)))) := by
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
  have u4 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x68 + ((-1) * x78)) ≥ 1) := by
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
  have h := NineTheoryTrial.th11991 t x01 x02 x03 x27 x35 x56 x68 x78
  exact (fun hh => (fun hh => hh u8) (hh (And.intro u7 (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u4 (And.intro u3 (And.intro u1 u6))))))))) h

theorem clause16030 (t x25 x56 x57 : ℝ) : (((t + ((-1) * x25)) ≤ 0) ∨ ((t + ((-1) * x56) + x57) ≥ 1) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ (x57 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x25)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x56) + x57) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x57 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th11992 t x25 x56 x57
  exact (fun hh => u1 (hh (And.intro u0 (And.intro u3 u2)))) h

theorem clause16031 (t x05 x13 x15 x34 x35 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + x34 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x15)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
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
  have h := NineTheoryTrial.th11994 t x05 x13 x15 x34 x35 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u3 (And.intro u1 (And.intro u5 (And.intro u4 u6)))))))) h

theorem clause16032 (t x01 x02 x13 x24 x36 x47 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + ((-1) * x47) + x67) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x47) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th11996 t x01 x02 x13 x24 x36 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u6 (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u7 u4))))))))) h

theorem clause16033 (t x05 x35 x45 : ℝ) : ((¬ ((t + x35 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x45)) ≤ 0)) ∨ ((t + ((-1) * x05) + x35) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + x35 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x05) + x35) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th11997 t x05 x35 x45
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause16034 (t x03 x13 x16 x34 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ ((t + ((-1) * x03)) ≤ 0) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ (x34 ≥ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x16)) ≤ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x03)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x67)) ≥ 1) := by
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
  have h := NineTheoryTrial.th11998 t x03 x13 x16 x34 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u4 (And.intro u2 (And.intro u1 (And.intro u5 (And.intro u7 u6))))))))) h

theorem clause16035 (t x36 x37 x56 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x36) + x56) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x36) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th12002 t x36 x37 x56 x67 x78
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u2 (And.intro u4 (And.intro u1 (And.intro u0 u3)))))) h

theorem clause16036 (t x01 x02 x13 x25 x37 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + ((-1) * x37) + x67) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1)))) := by
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
  have u3 : ((x02 + ((-1) * x25)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x37) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x13 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th12005 t x01 x02 x13 x25 x37 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u6 (And.intro u4 (And.intro u7 (And.intro u3 (And.intro u2 u5))))))))) h

theorem clause16037 (t x01 x02 x03 x13 x24 x35 x36 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((t + x45 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x45 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th12006 t x01 x02 x03 x13 x24 x35 x36 x45 x46
  exact (fun hh => (fun hh => hh u7) (hh (And.intro u3 (And.intro u6 (And.intro u8 (And.intro u9 (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u5 u2)))))))))) h

theorem clause16038 (t x06 x24 x26 x34 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x24 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x26)) ≤ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x24 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th12007 t x06 x24 x26 x34 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u3 (And.intro u5 (And.intro u4 u6)))))))) h

theorem clause16039 (t x01 x02 x13 x26 x35 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1)))) := by
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
  have u7 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th12008 t x01 x02 x13 x26 x35 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u4 (And.intro u1 (And.intro u5 (And.intro u0 (And.intro u7 (And.intro u3 u6))))))))) h

theorem clause16040 (x12 x26 x27 : ℝ) : ((¬ ((x26 + ((-1) * x27)) ≥ 0)) ∨ ((x12 + ((-1) * x27)) ≥ 1) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x26 + ((-1) * x27)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x27)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th12014 x12 x26 x27
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause16041 (t x02 x24 x26 x34 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x24 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x24 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th12015 t x02 x24 x26 x34 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u2 u3))))))) h

theorem clause16042 (t x01 x06 x12 x13 x26 x35 x58 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x26)) ≤ 0)) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x58) + x78) ≥ 1)) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
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
  have u3 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x58) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th12016 t x01 x06 x12 x13 x26 x35 x58 x67 x78
  exact (fun hh => (fun hh => hh u9) (hh (And.intro u6 (And.intro u1 (And.intro u8 (And.intro u2 (And.intro u7 (And.intro u5 (And.intro u10 (And.intro u3 (And.intro u0 u4))))))))))) h

theorem clause16043 (t x01 x13 x34 x35 x37 x46 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ ((t + ((-1) * x46)) ≤ 0) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x34 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x57) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x34 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th12017 t x01 x13 x34 x35 x37 x46 x57 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u6 (And.intro u5 (And.intro u4 (And.intro u10 (And.intro u1 (And.intro u9 (And.intro u2 (And.intro u7 (And.intro u3 u8)))))))))))) h

theorem clause16044 (t x01 x02 x03 x04 x12 x14 x26 x27 x45 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((t + x27 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((t + x27 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th12018 t x01 x02 x03 x04 x12 x14 x26 x27 x45 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u6 (And.intro u1 (And.intro u4 (And.intro u9 (And.intro u11 (And.intro u10 (And.intro u7 u3))))))))))))) h

theorem clause16045 (t x03 x06 x12 x13 x24 x26 x35 x36 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x36) + x46) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ (x03 ≥ 0)) ∨ (¬ ((x06 + ((-1) * x26)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
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
  have u7 : ((x24 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : (x03 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x06 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th12022 t x03 x06 x12 x13 x24 x26 x35 x36 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u10 (And.intro u5 (And.intro u0 (And.intro u3 (And.intro u8 (And.intro u1 (And.intro u11 (And.intro u2 (And.intro u9 (And.intro u4 (And.intro u6 u7))))))))))))) h

theorem clause16046 (t x03 x34 x35 x45 x56 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ (x45 ≥ 0))) := by
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
  have u3 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th12024 t x03 x34 x35 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u4 u6)))))))) h

theorem clause16048 (x13 x14 x35 x45 : ℝ) : ((¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((x35 + ((-1) * x45)) ≥ 0)) ∨ ((x14 + ((-1) * x45)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((x14 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th12029 x13 x14 x35 x45
  exact (fun hh => u3 (hh (And.intro u1 (And.intro u2 u0)))) h

theorem clause16049 (t x03 x05 x12 x23 x35 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ ((t + ((-1) * x57)) ≤ 0)) := by
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
  have u6 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th12030 t x03 x05 x12 x23 x35 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u8 (And.intro u0 (And.intro u7 (And.intro u5 (And.intro u3 (And.intro u1 u6)))))))))) h

theorem clause16050 (t x02 x03 x12 x23 x25 x36 x57 x67 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x02) + x12) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
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
  have u5 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th12035 t x02 x03 x12 x23 x25 x36 x57 x67
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u6 (And.intro u4 (And.intro u5 (And.intro u7 (And.intro u8 (And.intro u0 (And.intro u1 u3))))))))) h

theorem clause16051 (t x01 x04 x05 x12 x14 x23 x35 x47 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x05) ≥ 1)) ∨ ((t + ((-1) * x57)) ≤ 0)) := by
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
  have u3 : ((x04 + ((-1) * x47)) ≥ 1) := by
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
  have u6 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((t + ((-1) * x01) + x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th12040 t x01 x04 x05 x12 x14 x23 x35 x47 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u4 (And.intro u3 (And.intro u7 (And.intro u0 (And.intro u5 (And.intro u11 (And.intro u1 (And.intro u2 (And.intro u6 (And.intro u10 u9))))))))))))) h

theorem clause16052 (t x01 x05 x14 x35 x47 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + x47 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x05) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x14)) ≥ 1) := by
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
  have u5 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x47 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x01) + x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th12041 t x01 x05 x14 x35 x47 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u7 (And.intro u1 (And.intro u5 (And.intro u4 (And.intro u3 (And.intro u0 u2))))))))) h

theorem clause16053 (t x01 x03 x14 x35 x47 x56 x67 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + x47 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
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
  have u5 : ((t + x47 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th12042 t x01 x03 x14 x35 x47 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u7 (And.intro u4 (And.intro u1 (And.intro u2 (And.intro u0 u6))))))))) h

theorem clause16054 (t x01 x03 x04 x12 x14 x23 x35 x47 x56 x67 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x14)) ≤ 0))) := by
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
  have u7 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x14 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x01 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x12 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th12043 t x01 x03 x04 x12 x14 x23 x35 x47 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u10 (And.intro u0 (And.intro u6 (And.intro u5 (And.intro u7 (And.intro u1 (And.intro u9 (And.intro u3 (And.intro u8 (And.intro u2 u11))))))))))))) h

theorem clause16055 (t x02 x03 x12 x23 x26 x34 x47 x67 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x02) + x12) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((t + ((-1) * x47) + x67) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
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
  have u3 : ((t + ((-1) * x02) + x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x47) + x67) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th12045 t x02 x03 x12 x23 x26 x34 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u6 (And.intro u1 (And.intro u0 (And.intro u7 (And.intro u5 (And.intro u8 (And.intro u4 u2)))))))))) h

theorem clause16057 (t x02 x12 x25 x26 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ (x67 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th12049 t x02 x12 x25 x26 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u2 (And.intro u5 (And.intro u0 (And.intro u1 (And.intro u3 u4)))))))) h

theorem clause16058 (x35 x45 x56 : ℝ) : ((¬ ((x35 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ ((x45 + ((-1) * x56)) ≤ (-1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x45 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th12051 x35 x45 x56
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause16059 (t x01 x04 x12 x14 x26 x34 x45 x46 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ ((x14 + ((-1) * x34)) ≥ 0) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((t + x67 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x45 ≥ 0)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x34)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x67 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th12052 t x01 x04 x12 x14 x26 x34 x45 x46 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u9 (And.intro u6 (And.intro u4 (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u7 (And.intro u10 (And.intro u8 (And.intro u2 (And.intro u11 u5))))))))))))) h

theorem clause16060 (t x03 x13 x34 x35 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0)) := by
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
  have u4 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th12056 t x03 x13 x34 x35 x56
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u1 (And.intro u5 (And.intro u3 (And.intro u0 (And.intro u6 u2))))))) h

theorem clause16061 (t x03 x04 x13 x15 x34 x35 x45 x56 x57 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x03) + x13) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1))) := by
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
  have u5 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x56) + x57) ≥ 1) := by
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
  have h := NineTheoryTrial.th12058 t x03 x04 x13 x15 x34 x35 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u9 (And.intro u3 (And.intro u0 (And.intro u7 (And.intro u8 (And.intro u6 (And.intro u2 (And.intro u4 u5))))))))))) h

theorem clause16062 (t x03 x05 x13 x16 x26 x34 x35 x36 x46 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x03) + x13) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x46 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((t + x67 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((x16 + ((-1) * x26)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x03) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x67 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x05 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x16 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))))
  have u12 : ((x16 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))))
  have h := NineTheoryTrial.th12060 t x03 x05 x13 x16 x26 x34 x35 x36 x46 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u8 (And.intro u7 (And.intro u9 (And.intro u5 (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u6 (And.intro u10 (And.intro u4 (And.intro u11 u12)))))))))))))) h

theorem clause16063 (t x06 x25 x26 x45 x56 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x25 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x26)) ≤ 0)) ∨ (¬ ((x26 + ((-1) * x68)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x25 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th12061 t x06 x25 x26 x45 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u6 (And.intro u4 u2)))))))) h

theorem clause16064 (t x03 x34 x35 x45 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x45) + x47) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x45)) ≤ 0) := by
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
  have u4 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x45) + x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th12062 t x03 x34 x35 x45 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u3 u1))))))) h

theorem clause16065 (t x02 x13 x23 x24 x34 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((t + x13 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1))) := by
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
  have u3 : ((x24 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th12063 t x02 x13 x23 x24 x34
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u1 u4)))))) h

theorem clause16067 (t x03 x04 x13 x34 x36 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x03) + x13) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x03) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x46) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th12066 t x03 x04 x13 x34 x36 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u7 (And.intro u8 (And.intro u5 (And.intro u6 u3)))))))))) h

theorem clause16068 (t x01 x02 x05 x15 x24 x47 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x47) + x57) ≥ 1)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1))) := by
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
  have u3 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x47) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x01) + x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x15 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th12069 t x01 x02 x05 x15 x24 x47 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u8 (And.intro u6 (And.intro u3 (And.intro u5 (And.intro u7 (And.intro u1 u2)))))))))) h

theorem clause16069 (t x03 x15 x35 x37 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + x15 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x57)) ≥ 0)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x15 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x37 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th12070 t x03 x15 x35 x37 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u1 u4))))))) h

theorem clause16070 (t x04 x13 x24 x34 x37 x45 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((t + ((-1) * x45) + x47) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x47)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x45) + x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x37 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th12071 t x04 x13 x24 x34 x37 x45 x47
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u6 (And.intro u3 (And.intro u7 u2)))))))) h

theorem clause16071 (t x03 x07 x13 x15 x35 x37 x56 x68 x78 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x03) + x13) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x07 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + x68 + ((-1) * x78)) ≥ 1))) := by
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
  have u3 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x07 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + x68 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th12073 t x03 x07 x13 x15 x35 x37 x56 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u9 (And.intro u1 (And.intro u7 (And.intro u8 (And.intro u6 (And.intro u3 (And.intro u4 (And.intro u5 u0))))))))))) h

theorem clause16072 (t x03 x05 x06 x13 x15 x35 x36 x56 x67 x68 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x03) + x13) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x06)) ≥ 0)) ∨ ((t + ((-1) * x05)) ≤ 0) ∨ (¬ ((x06 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ (x67 ≥ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
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
  have u3 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x05)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x06 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x15 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th12074 t x03 x05 x06 x13 x15 x35 x36 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u6 (And.intro u1 (And.intro u5 (And.intro u11 (And.intro u7 (And.intro u10 (And.intro u4 (And.intro u9 (And.intro u2 (And.intro u8 u0))))))))))))) h

theorem clause16073 (t x03 x13 x34 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ ((t + ((-1) * x03)) ≤ 0) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x67 ≥ 0))) := by
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
  have u3 : ¬ ((t + ((-1) * x03)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
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
  have h := NineTheoryTrial.th12076 t x03 x13 x34 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u6 u4)))))))) h

theorem clause16074 (t x03 x05 x12 x14 x25 x34 x46 x57 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x14 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ ((t + ((-1) * x03)) ≤ 0) ∨ (¬ ((x05 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + x68 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x03)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((t + x68 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th12080 t x03 x05 x12 x14 x25 x34 x46 x57 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u11 (And.intro u9 (And.intro u5 (And.intro u1 (And.intro u6 (And.intro u7 (And.intro u8 u10))))))))))))) h

theorem clause16075 (t x02 x03 x12 x13 x25 x27 x36 x37 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x03)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x27) + x37) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x03)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x27) + x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x02 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th12081 t x02 x03 x12 x13 x25 x27 x36 x37
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u5 (And.intro u9 (And.intro u6 (And.intro u2 (And.intro u4 (And.intro u7 (And.intro u3 u8))))))))))) h

theorem clause16076 (t x03 x05 x07 x12 x13 x25 x34 x37 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ ((t + ((-1) * x03)) ≤ 0) ∨ (¬ ((x05 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((t + x37 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1)))) := by
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
  have u3 : ¬ ((t + ((-1) * x03)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + x37 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x05 + ((-1) * x07)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th12082 t x03 x05 x07 x12 x13 x25 x34 x37 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u8 (And.intro u2 (And.intro u1 (And.intro u11 (And.intro u6 (And.intro u7 (And.intro u10 (And.intro u5 (And.intro u9 u4))))))))))))) h

theorem clause16077 (t x05 x07 x45 x56 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x07)) ≥ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ (x67 ≥ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x07)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x07 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th12093 t x05 x07 x45 x56 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u6 (And.intro u7 (And.intro u3 (And.intro u4 (And.intro u2 u1))))))))) h

theorem clause16078 (t x04 x05 x07 x13 x15 x34 x45 x47 x56 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x47) + x57) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x15)) ≥ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x47) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x04 + ((-1) * x07)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x15 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x05 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))))
  have u12 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))))
  have h := NineTheoryTrial.th12094 t x04 x05 x07 x13 x15 x34 x45 x47 x56 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u10 (And.intro u5 (And.intro u6 (And.intro u9 (And.intro u7 (And.intro u12 (And.intro u8 (And.intro u11 (And.intro u4 (And.intro u3 (And.intro u2 u1)))))))))))))) h

theorem clause16079 (t x01 x03 x13 x16 x34 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((t + x13 + ((-1) * x16)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x13 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th12096 t x01 x03 x13 x16 x34
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u2 u5)))))) h

theorem clause16080 (t x01 x03 x12 x13 x17 x34 x37 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x37) + x57) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1))) := by
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
  have u3 : ((x03 + ((-1) * x34)) ≥ 1) := by
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
  have u6 : ((t + ((-1) * x37) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th12099 t x01 x03 x12 x13 x17 x34 x37 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u10 (And.intro u7 (And.intro u0 (And.intro u5 (And.intro u9 (And.intro u6 (And.intro u4 (And.intro u8 (And.intro u1 (And.intro u2 u3)))))))))))) h

theorem clause16081 (x03 x23 x37 : ℝ) : ((¬ ((x03 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ ((x03 + ((-1) * x37)) ≤ (-1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x03 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th12100 x03 x23 x37
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause16082 (t x01 x02 x15 x24 x48 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x01) + x02) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((t + ((-1) * x48) + x78) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x48)) ≤ (-1)))) := by
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
  have u7 : ((x24 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th12102 t x01 x02 x15 x24 x48 x57 x78
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u4 (And.intro u5 (And.intro u6 (And.intro u1 (And.intro u0 (And.intro u2 u7)))))))) h

theorem clause16083 (t x01 x03 x12 x14 x23 x35 x47 x58 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ (x12 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x58) + x78) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
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
  have u4 : ((x14 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x35 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x58) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th12107 t x01 x03 x12 x14 x23 x35 x47 x58 x78
  exact (fun hh => (fun hh => hh u7) (hh (And.intro u6 (And.intro u3 (And.intro u2 (And.intro u8 (And.intro u9 (And.intro u4 (And.intro u5 (And.intro u0 (And.intro u1 u10))))))))))) h

theorem clause16085 (t x06 x14 x16 x45 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x45 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x16)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x45 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th12114 t x06 x14 x16 x45 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u3 (And.intro u4 (And.intro u5 (And.intro u2 (And.intro u1 u0)))))))) h

theorem clause16086 (t x01 x03 x16 x35 x58 x67 x78 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x58) + x78) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x16)) ≥ 1) := by
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
  have u6 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th12116 t x01 x03 x16 x35 x58 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u6 (And.intro u0 (And.intro u7 (And.intro u1 (And.intro u3 u5))))))))) h

theorem clause16087 (t x16 x36 x37 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x36 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((t + x16 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x36 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x16 + ((-1) * x36)) ≥ 1) := by
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
  have h := NineTheoryTrial.th12118 t x16 x36 x37 x67 x78
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u3 (And.intro u2 (And.intro u5 (And.intro u0 u1)))))) h

theorem clause16088 (t x01 x02 x03 x27 x35 x57 x67 x78 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
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
  have u4 : ((t + ((-1) * x57) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th12120 t x01 x02 x03 x27 x35 x57 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u8 (And.intro u7 (And.intro u3 (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u4 u6)))))))))) h

theorem clause16089 (t x01 x02 x04 x12 x13 x26 x27 x34 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + x27 + ((-1) * x57)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x02)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x27 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x12 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th12140 t x01 x02 x04 x12 x13 x26 x27 x34 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u7 (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u4 (And.intro u10 (And.intro u9 (And.intro u11 (And.intro u2 u6))))))))))))) h

theorem clause16090 (t x01 x04 x13 x17 x34 x45 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
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
  have u4 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x57) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th12141 t x01 x04 x13 x17 x34 x45 x57 x67 x78
  exact (fun hh => (fun hh => hh u8) (hh (And.intro u2 (And.intro u4 (And.intro u6 (And.intro u3 (And.intro u5 (And.intro u7 (And.intro u10 (And.intro u0 (And.intro u9 u1))))))))))) h

theorem clause16091 (t x01 x02 x12 x17 x24 x27 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ (¬ (x24 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x17)) ≤ 0)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x02)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x17)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th12142 t x01 x02 x12 x17 x24 x27 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u8 (And.intro u7 (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u3 (And.intro u6 u4)))))))))) h

theorem clause16093 (t x06 x12 x23 x26 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ ((t + ((-1) * x06)) ≤ 0) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
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
  have u3 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x06)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th12145 t x06 x12 x23 x26 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u6 (And.intro u3 (And.intro u5 u1)))))))) h

theorem clause16094 (t x02 x14 x24 x26 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((t + x45 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x45 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x26 + ((-1) * x46)) ≤ 0) := by
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
  have u6 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th12146 t x02 x14 x24 x26 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u4 (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u5 u3)))))))) h

theorem clause16095 (t x01 x03 x04 x06 x12 x16 x23 x34 x45 x46 x67 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ ((t + ((-1) * x46)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x06)) ≥ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x16)) ≤ 0))) := by
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
  have u3 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x01 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))))
  have u12 : ((x12 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))))
  have h := NineTheoryTrial.th12152 t x01 x03 x04 x06 x12 x16 x23 x34 x45 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u11 (And.intro u4 (And.intro u3 (And.intro u9 (And.intro u12 (And.intro u5 (And.intro u8 (And.intro u6 (And.intro u2 (And.intro u7 (And.intro u0 u10)))))))))))))) h

theorem clause16096 (t x24 x25 x34 x45 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x24 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x24 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th12153 t x24 x25 x34 x45 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u4 (And.intro u0 u5))))))) h

theorem clause16097 (t x12 x13 x14 : ℝ) : ((¬ ((x13 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ ((t + ((-1) * x12) + x14) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x13 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((t + ((-1) * x12) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x12) + x14) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th12154 t x12 x13 x14
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause16098 (t x01 x07 x12 x26 x37 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + ((-1) * x37) + x67) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x07) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x37) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x01) + x07) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th12155 t x01 x07 x12 x26 x37 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u7 (And.intro u4 (And.intro u0 (And.intro u1 (And.intro u6 (And.intro u5 u3))))))))) h

theorem clause16099 (t x05 x12 x23 x25 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x05 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1)))) := by
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
  have u3 : ((x05 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th12156 t x05 x12 x23 x25 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u5 (And.intro u4 (And.intro u3 (And.intro u0 (And.intro u6 u7))))))))) h

theorem clause16100 (t x06 x25 x26 x35 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x25 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((x25 + ((-1) * x26)) ≤ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x25 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th12157 t x06 x25 x26 x35 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u6 (And.intro u0 (And.intro u1 (And.intro u3 u4)))))))) h

theorem clause16101 (t x02 x04 x06 x26 x34 x45 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + ((-1) * x02) + x04) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + x26 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x06)) ≥ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1)))) := by
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
  have u3 : ((t + ((-1) * x02) + x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x26 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th12160 t x02 x04 x06 x26 x34 x45 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u8 (And.intro u6 u7)))))))))) h

theorem clause16102 (t x01 x03 x04 x16 x34 x45 x47 x67 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x47) + x67) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x01) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x45)) ≥ 1) := by
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
  have u5 : ((t + ((-1) * x47) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th12161 t x01 x03 x04 x16 x34 x45 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u3 (And.intro u5 (And.intro u0 (And.intro u8 (And.intro u7 (And.intro u1 (And.intro u4 u2)))))))))) h

theorem clause16103 (t x04 x06 x12 x16 x23 x24 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((t + x23 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x06)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x16)) ≤ 0))) := by
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
  have u4 : ((x04 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th12162 t x04 x06 x12 x16 x23 x24 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u6 (And.intro u3 (And.intro u7 (And.intro u0 (And.intro u2 u1))))))))) h

theorem clause16104 (t x07 x12 x23 x27 x37 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x07 + ((-1) * x27)) ≥ 0)) ∨ ((t + ((-1) * x37)) ≤ 0)) := by
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
  have u3 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 + ((-1) * x27)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x37)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th12163 t x07 x12 x23 x27 x37 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u7 (And.intro u4 (And.intro u2 (And.intro u3 (And.intro u6 (And.intro u0 u5))))))))) h

theorem clause16105 (t x04 x12 x23 x24 x34 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1)))) := by
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
  have u3 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th12164 t x04 x12 x23 x24 x34 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u6 (And.intro u4 (And.intro u2 (And.intro u1 (And.intro u7 (And.intro u0 u5))))))))) h

theorem clause16106 (t x06 x12 x24 x26 x34 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x24 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x24 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th12165 t x06 x12 x24 x26 x34 x46
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u6 (And.intro u0 (And.intro u2 (And.intro u1 (And.intro u5 u3))))))) h

theorem clause16107 (x01 x12 x16 : ℝ) : ((¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ ((x01 + ((-1) * x16)) ≥ 1) ∨ (¬ ((x12 + ((-1) * x16)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x16)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th12166 x01 x12 x16
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause16108 (t x01 x02 x04 x12 x24 x26 x34 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x24 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x01) + x04) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x02)) ≥ 0) := by
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
  have u4 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x01) + x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th12168 t x01 x02 x04 x12 x24 x26 x34 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u6 (And.intro u7 (And.intro u4 (And.intro u8 u5)))))))))) h

theorem clause16109 (t x01 x12 x23 x37 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x67)) ≥ 0)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
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
  have u3 : ((x37 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x37)) ≥ 1) := by
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
  have h := NineTheoryTrial.th12169 t x01 x12 x23 x37 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u7 (And.intro u6 (And.intro u2 (And.intro u3 (And.intro u5 u1))))))))) h

theorem clause16110 (t x06 x24 x26 x45 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x45 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x26)) ≤ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x45 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th12170 t x06 x24 x26 x45 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u6 (And.intro u0 (And.intro u4 (And.intro u3 u1)))))))) h

theorem clause16111 (x34 x35 x36 : ℝ) : ((¬ ((x35 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x35)) ≥ 0)) ∨ ((x34 + ((-1) * x36)) ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x34 + ((-1) * x36)) ≥ 0) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th12174 x34 x35 x36
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause16112 (t x02 x03 x04 x12 x15 x23 x25 x34 x45 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x02) + x12) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x25)) ≤ 0)) ∨ (¬ (x67 ≥ 0))) := by
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
  have u6 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x15 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))))
  have u12 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))))
  have h := NineTheoryTrial.th12175 t x02 x03 x04 x12 x15 x23 x25 x34 x45 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u5 (And.intro u3 (And.intro u0 (And.intro u8 (And.intro u4 (And.intro u1 (And.intro u10 (And.intro u11 (And.intro u6 (And.intro u9 (And.intro u2 u12)))))))))))))) h

theorem clause16113 (t x02 x03 x06 x23 x34 x36 x46 x56 x67 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((t + x02 + ((-1) * x06)) ≥ 1))) := by
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
  have u4 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x46) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + x02 + ((-1) * x06)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th12177 t x02 x03 x06 x23 x34 x36 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u7 (And.intro u4 (And.intro u5 (And.intro u9 (And.intro u0 (And.intro u3 (And.intro u6 (And.intro u2 u8))))))))))) h

theorem clause16114 (x12 x13 x24 x34 : ℝ) : ((¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x24 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th12178 x12 x13 x24 x34
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u1 (And.intro u0 u2)))) h

theorem clause16116 (t x03 x06 x23 x34 x36 x46 x56 x67 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((t + x03 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x36)) ≤ 0))) := by
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
  have u3 : ((t + x03 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x46) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x06 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th12180 t x03 x06 x23 x34 x36 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u6 (And.intro u4 (And.intro u8 (And.intro u7 (And.intro u5 (And.intro u3 (And.intro u0 u2)))))))))) h

theorem clause16119 (t x01 x03 x12 x13 x26 x34 x37 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + ((-1) * x37) + x67) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
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
  have u3 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x13 ≥ 0) := by
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
  have h := NineTheoryTrial.th12183 t x01 x03 x12 x13 x26 x34 x37 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u6 (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u4 (And.intro u9 u7))))))))))) h

theorem clause16120 (t x02 x12 x25 x27 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1)) ∨ (¬ (x78 ≥ 0)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th12184 t x02 x12 x25 x27 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u6 u5)))))))) h

theorem clause16121 (t x03 x06 x13 x34 x36 x45 x46 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x36 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x06)) ≤ 0)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x06 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1))) := by
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
  have u4 : ((x36 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x06 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th12186 t x03 x06 x13 x34 x36 x45 x46 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u4 (And.intro u6 (And.intro u8 (And.intro u9 (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u5 u3))))))))))) h

theorem clause16122 (t x02 x04 x07 x12 x13 x25 x27 x34 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((t + x27 + ((-1) * x47)) ≥ 1))) := by
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
  have u4 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x04 + ((-1) * x07)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x12 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((t + x27 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th12187 t x02 x04 x07 x12 x13 x25 x27 x34 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u10 (And.intro u9 (And.intro u11 (And.intro u6 (And.intro u0 (And.intro u8 (And.intro u7 (And.intro u2 (And.intro u3 u1))))))))))))) h

theorem clause16123 (t x03 x13 x34 x37 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
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
  have u4 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th12188 t x03 x13 x34 x37 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u6 (And.intro u2 (And.intro u0 (And.intro u4 u5)))))))) h

theorem clause16124 (t x01 x16 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1))) ∨ (¬ (x67 ≥ 0)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x16 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th12189 t x01 x16 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u5 u6)))))))) h

theorem clause16125 (t x01 x03 x13 x15 x34 x37 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + ((-1) * x37) + x67) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1)))) := by
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
  have u4 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x37) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th12190 t x01 x03 x13 x15 x34 x37 x56 x67
  exact (fun hh => (fun hh => hh u9) (hh (And.intro u4 (And.intro u8 (And.intro u0 (And.intro u7 (And.intro u5 (And.intro u3 (And.intro u2 (And.intro u6 u1)))))))))) h

theorem clause16127 (t x03 x13 x34 x36 x68 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ ((t + ((-1) * x68)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1)))) := by
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
  have u5 : ¬ ((t + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th12193 t x03 x13 x34 x36 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u0 (And.intro u2 (And.intro u3 (And.intro u4 u6)))))))) h

theorem clause16128 (t x01 x04 x07 x12 x13 x26 x34 x47 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((t + ((-1) * x47) + x67) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x07)) ≤ 0)) ∨ ((t + ((-1) * x01)) ≤ 0) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
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
  have u3 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x47) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x04 + ((-1) * x07)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th12194 t x01 x04 x07 x12 x13 x26 x34 x47 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u2 (And.intro u0 (And.intro u10 (And.intro u8 (And.intro u5 (And.intro u1 (And.intro u4 (And.intro u3 (And.intro u11 (And.intro u9 u7))))))))))))) h

theorem clause16129 (t x05 x26 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x05)) ≤ 0) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x68)) ≤ (-1))) ∨ (¬ (x67 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x05)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th12195 t x05 x26 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u6 (And.intro u3 u5)))))))) h

theorem clause16130 (t x01 x02 x03 x13 x25 x26 x34 x36 x56 x67 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((t + ((-1) * x36) + x56) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x26)) ≥ 0)) ∨ ((t + ((-1) * x01)) ≤ 0)) := by
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
  have u3 : ((x01 + ((-1) * x02)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x36) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x25 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th12196 t x01 x02 x03 x13 x25 x26 x34 x36 x56 x67
  exact (fun hh => (fun hh => hh u9) (hh (And.intro u7 (And.intro u5 (And.intro u0 (And.intro u8 (And.intro u11 (And.intro u1 (And.intro u4 (And.intro u3 (And.intro u10 (And.intro u6 u2)))))))))))) h

theorem clause16131 (t x03 x36 x37 x56 x67 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x36) + x56) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x67)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x36) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th12197 t x03 x36 x37 x56 x67
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u1 u4)))))) h

theorem clause16132 (t x02 x12 x23 x26 x34 x45 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x02) + x12) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x56 ≥ 0)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1))) := by
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
  have u3 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th12200 t x02 x12 x23 x26 x34 x45 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u4 (And.intro u7 (And.intro u1 (And.intro u5 (And.intro u9 (And.intro u6 (And.intro u8 u2))))))))))) h

theorem clause16133 (t x02 x12 x23 x25 x26 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ ((t + ((-1) * x26)) ≤ 0)) := by
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
  have u3 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x26)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th12201 t x02 x12 x23 x25 x26
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u1 (And.intro u3 u2)))))))) h

theorem clause16134 (t x02 x12 x24 x25 x26 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ ((t + ((-1) * x26)) ≤ 0) ∨ (¬ (x25 ≥ 0))) := by
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
  have u3 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x26)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x25 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th12202 t x02 x12 x24 x25 x26
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u6 (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u3 u1)))))))) h

theorem clause16135 (t x01 x03 x16 x34 x45 x57 x67 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
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
  have u3 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
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
  have u6 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th12204 t x01 x03 x16 x34 x45 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u3 (And.intro u5 (And.intro u6 (And.intro u7 (And.intro u1 u4))))))))) h

theorem clause16136 (t x01 x03 x06 x12 x16 x24 x34 x45 x56 x67 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ (x24 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x06)) ≥ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x16)) ≤ 0))) := by
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
  have u3 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x24 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x01 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x12 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th12205 t x01 x03 x06 x12 x16 x24 x34 x45 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u11 (And.intro u8 (And.intro u4 (And.intro u10 (And.intro u6 (And.intro u1 (And.intro u3 (And.intro u5 (And.intro u7 (And.intro u9 u0))))))))))))) h

theorem clause16137 (t x01 x03 x16 x34 x45 x56 x67 x78 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
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
  have u3 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th12206 t x01 x03 x16 x34 x45 x56 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u0 (And.intro u9 (And.intro u8 (And.intro u6 (And.intro u7 (And.intro u1 u5))))))))))) h

theorem clause16139 (t x01 x02 x03 x12 x23 x26 x34 x45 x56 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
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
  have u3 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x02)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th12208 t x01 x02 x03 x12 x23 x26 x34 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u1 (And.intro u8 (And.intro u6 (And.intro u7 (And.intro u10 (And.intro u3 (And.intro u9 u4)))))))))))) h

theorem clause16140 (t x01 x03 x12 x25 x34 x46 x56 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1))) := by
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
  have u5 : ((t + ((-1) * x46) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th12209 t x01 x03 x12 x25 x34 x46 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u3 (And.intro u6 (And.intro u4 (And.intro u2 u7))))))))) h

theorem clause16141 (t x02 x12 x16 x24 x26 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x24 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x16)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x24 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th12210 t x02 x12 x16 x24 x26 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u7 (And.intro u0 (And.intro u2 (And.intro u1 (And.intro u4 (And.intro u6 u3))))))))) h

theorem clause16142 (t x01 x02 x03 x12 x25 x27 x34 x47 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((t + x27 + ((-1) * x47)) ≥ 1))) := by
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
  have h := NineTheoryTrial.th12211 t x01 x02 x03 x12 x25 x27 x34 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u7 (And.intro u3 (And.intro u5 (And.intro u1 (And.intro u8 (And.intro u2 (And.intro u6 u0)))))))))) h

theorem clause16143 (t x01 x03 x16 x34 x46 x56 x67 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
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
  have u4 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x46) + x56) ≥ 1) := by
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
  have h := NineTheoryTrial.th12212 t x01 x03 x16 x34 x46 x56 x67
  exact (fun hh => (fun hh => hh u7) (hh (And.intro u5 (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u4 (And.intro u6 u0)))))))) h

theorem clause16144 (t x02 x04 x12 x23 x24 x26 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0)) := by
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
  have u3 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x46) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th12213 t x02 x04 x12 x23 x24 x26 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u1 (And.intro u7 (And.intro u4 (And.intro u10 (And.intro u6 (And.intro u8 u9)))))))))))) h

theorem clause16145 (x01 x02 x05 : ℝ) : (((x01 + ((-1) * x05)) ≥ 0) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x05)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x05)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x02)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th12214 x01 x02 x05
  exact (fun hh => u0 (hh (And.intro u2 u1))) h

theorem clause16146 (t x01 x03 x12 x26 x34 x47 x67 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((t + ((-1) * x47) + x67) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
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
  have u4 : ((t + ((-1) * x47) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th12215 t x01 x03 x12 x26 x34 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u5 (And.intro u3 (And.intro u2 (And.intro u4 (And.intro u0 (And.intro u1 u6))))))))) h

theorem clause16147 (t x01 x03 x05 x26 x34 x46 x56 x67 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((t + x26 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1)))) := by
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
  have u3 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x26 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th12216 t x01 x03 x05 x26 x34 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u8 (And.intro u5 (And.intro u6 (And.intro u0 (And.intro u2 (And.intro u1 (And.intro u7 u3)))))))))) h

theorem clause16148 (t x26 x36 x37 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x26 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x26 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th12217 t x26 x36 x37 x67 x78
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u0 u4)))))) h

#print axioms clause16148
end NineCNFDirectTrial
