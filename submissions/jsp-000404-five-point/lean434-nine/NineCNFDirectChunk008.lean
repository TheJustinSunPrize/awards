import NineTheoryTrial

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineCNFDirectTrial

theorem clause10794 (t x01 x13 x15 x34 x35 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x34) + x35) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
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
  have u3 : ((t + ((-1) * x34) + x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1658 t x01 x13 x15 x34 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u4 (And.intro u2 u3))))))) h

theorem clause10795 (x01 x13 x15 : ℝ) : ((¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x15)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1659 x01 x13 x15
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 u0)))) h

theorem clause10796 (t x01 x03 x12 x13 x16 x35 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
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
  have u5 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x57) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th1660 t x01 x03 x12 x13 x16 x35 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u8 (And.intro u1 (And.intro u7 (And.intro u6 (And.intro u0 (And.intro u4 u5)))))))))) h

theorem clause10797 (t x01 x07 x12 x17 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x07)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x17) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
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
  have u4 : ((x01 + ((-1) * x07)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x12) + x17) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1662 t x01 x07 x12 x17 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u2 u3))))))) h

theorem clause10798 (t x06 x36 x37 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x06 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x06 + ((-1) * x36)) ≥ 1) := by
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
  have h := NineTheoryTrial.th1665 t x06 x36 x37 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u5 u4))))))) h

theorem clause10799 (x06 : ℝ) (h : (x06 ≥ 0)) : ((x06 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause10800 (t x17 x26 x27 x36 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + x26 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x27)) ≤ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x27)) ≥ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x26 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x26 + ((-1) * x27)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 + ((-1) * x27)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1669 t x17 x26 x27 x36 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u2 (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u3 u4)))))))) h

theorem clause10801 (t x01 x03 x12 x13 x16 x36 x56 x67 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + x16 + ((-1) * x56)) ≥ 1))) := by
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
  have u7 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x16 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th1672 t x01 x03 x12 x13 x16 x36 x56 x67
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u6 (And.intro u8 (And.intro u3 (And.intro u7 (And.intro u4 (And.intro u1 (And.intro u0 u2))))))))) h

theorem clause10802 (t x01 x03 x12 x13 x17 x35 x58 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x58) + x78) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1))) := by
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
  have u5 : ((x35 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x58) + x78) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th1679 t x01 x03 x12 x13 x17 x35 x58 x78
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u8 (And.intro u2 (And.intro u4 (And.intro u7 (And.intro u1 (And.intro u6 (And.intro u3 u0))))))))) h

theorem clause10803 (t x01 x03 x05 x12 x13 x17 x35 x57 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x58)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + x17 + ((-1) * x57)) ≥ 1))) := by
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
  have u4 : ((x35 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 + ((-1) * x58)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th1680 t x01 x03 x05 x12 x13 x17 x35 x57 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u9 (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u6 (And.intro u7 (And.intro u3 u8))))))))))) h

theorem clause10804 (t x05 x06 x56 x58 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((t + ((-1) * x56) + x58) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x58)) ≥ 1) := by
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
  have u5 : ((t + ((-1) * x56) + x58) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1682 t x05 x06 x56 x58 x67
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u3 (And.intro u1 (And.intro u5 (And.intro u4 u0)))))) h

theorem clause10805 (t x01 x03 x12 x13 x15 x25 x35 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
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
  have u4 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x56) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x15 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th1683 t x01 x03 x12 x13 x15 x25 x35 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u6 (And.intro u3 (And.intro u0 (And.intro u9 (And.intro u5 (And.intro u7 (And.intro u1 (And.intro u2 u4))))))))))) h

theorem clause10806 (t x05 x35 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + ((-1) * x35) + x45) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1)))) := by
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
  have u3 : ((t + ((-1) * x35) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1686 t x05 x35 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u3 (And.intro u0 (And.intro u5 (And.intro u1 u2))))))) h

theorem clause10808 (t x06 x35 x56 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x67)) ≥ 0)) ∨ (¬ ((t + x06 + ((-1) * x56)) ≥ 1))) := by
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
  have u3 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x06 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1688 t x06 x35 x56 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u0))))))) h

theorem clause10809 (t x01 x03 x05 x12 x13 x16 x35 x56 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x03 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ (x67 ≥ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
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
  have u5 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x03 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th1689 t x01 x03 x05 x12 x13 x16 x35 x56 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u11 (And.intro u10 (And.intro u0 (And.intro u4 (And.intro u9 (And.intro u1 (And.intro u6 (And.intro u7 (And.intro u3 (And.intro u2 u5))))))))))))) h

theorem clause10810 (t x01 x12 x16 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1691 t x01 x12 x16 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u6 (And.intro u5 (And.intro u1 u2)))))))) h

theorem clause10812 (t x01 x03 x07 x12 x13 x15 x25 x37 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((t + ((-1) * x37) + x57) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1)))) := by
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
  have u4 : ((x15 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x37) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x03 + ((-1) * x07)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th1695 t x01 x03 x07 x12 x13 x15 x25 x37 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u7 (And.intro u4 (And.intro u8 (And.intro u6 (And.intro u0 (And.intro u2 (And.intro u9 (And.intro u1 (And.intro u10 u5)))))))))))) h

theorem clause10813 (t x03 x23 x27 x37 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x03) + x23) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x27)) ≤ 0)) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x03) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x37)) ≥ 1) := by
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
  have h := NineTheoryTrial.th1696 t x03 x23 x27 x37 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u4 (And.intro u2 u5))))))) h

theorem clause10814 (x27 x37 x78 : ℝ) : ((¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x27 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x27 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1697 x27 x37 x78
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u2 u0))) h

theorem clause10815 (x02 x23 x27 : ℝ) : ((¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x27)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x27)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1698 x02 x23 x27
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 u0)))) h

theorem clause10816 (t x03 x35 x37 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x57)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1))) := by
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
  have u3 : ((t + ((-1) * x56) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1699 t x03 x35 x37 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u4 (And.intro u5 u2))))))) h

theorem clause10817 (t x03 x05 x34 x35 x37 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((t + ((-1) * x34) + x37) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x34) + x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1701 t x03 x05 x34 x35 x37 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u3 (And.intro u4 (And.intro u6 (And.intro u1 u2)))))))) h

theorem clause10818 (t x04 x34 x45 x46 x56 x68 : ℝ) : ((¬ ((x46 + ((-1) * x56)) ≤ 0)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ ((t + ((-1) * x68)) ≤ 0) ∨ (¬ (x04 ≥ 0)) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1)))) := by
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
  have u4 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x04 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1705 t x04 x34 x45 x46 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u7 (And.intro u2 (And.intro u6 (And.intro u1 (And.intro u4 u3))))))))) h

theorem clause10819 (t x01 x03 x04 x12 x13 x16 x34 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((t + x16 + ((-1) * x46)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
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
  have u5 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + x16 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th1707 t x01 x03 x04 x12 x13 x16 x34 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u9 (And.intro u8 (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u5 (And.intro u2 (And.intro u7 u6))))))))))) h

theorem clause10820 (t x04 x06 x34 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x04 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x04 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x46)) ≥ 1) := by
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
  have h := NineTheoryTrial.th1708 t x04 x06 x34 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u4 u0))))))) h

theorem clause10822 (t x01 x15 x16 x56 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ (x15 ≥ 0)) ∨ (¬ ((x16 + ((-1) * x68)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x15 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1710 t x01 x15 x16 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u6 (And.intro u4 u5)))))))) h

theorem clause10823 (x01 x03 x13 x16 : ℝ) : ((¬ ((x01 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x16)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th1711 x01 x03 x13 x16
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u2 u0))))) h

theorem clause10824 (t x01 x13 x14 x24 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x13)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ (x24 ≥ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x24 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th1712 t x01 x13 x14 x24 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u5 (And.intro u3 (And.intro u4 u6)))))))) h

theorem clause10825 (t x01 x02 x12 x14 x23 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x14) ≥ 1))) := by
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
  have u3 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x12) + x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1715 t x01 x02 x12 x14 x23
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u0 u4))))))) h

theorem clause10827 (t x04 x06 x45 x46 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x45 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x68)) ≤ (-1)))) := by
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
  have u4 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1719 t x04 x06 x45 x46 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u0 u5))))))) h

theorem clause10828 (t x14 x34 x45 x47 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x14 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1725 t x14 x34 x45 x47 x67 x78
  exact (fun hh => (fun hh => hh u7) (hh (And.intro u5 (And.intro u6 (And.intro u2 (And.intro u1 (And.intro u4 (And.intro u3 u0)))))))) h

theorem clause10829 (t x01 x05 x13 x15 x16 x17 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x13) + x15) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x15)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x17)) ≤ 0)) ∨ (¬ ((t + ((-1) * x67) + x68) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x68)) ≥ 1))) := by
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
  have u3 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x13) + x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x16 + ((-1) * x17)) ≤ 0) := by
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
  have h := NineTheoryTrial.th1730 t x01 x05 x13 x15 x16 x17 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u6 (And.intro u1 (And.intro u8 (And.intro u7 (And.intro u9 (And.intro u2 (And.intro u0 (And.intro u3 u5))))))))))) h

theorem clause10830 (t x01 x06 x13 x16 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x06)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((t + ((-1) * x13) + x16) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x68)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x13) + x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1732 t x01 x06 x13 x16 x68
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u3 u2)))))) h

theorem clause10831 (t x06 x14 x16 x45 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x45 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x16)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x16)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x45 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1738 t x06 x14 x16 x45 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u3 u6)))))))) h

theorem clause10832 (t x12 x14 x24 x27 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((t + ((-1) * x24) + x27) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x24) + x27) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1741 t x12 x14 x24 x27 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u3 (And.intro u2 u4))))))) h

theorem clause10833 (t x02 x12 x23 x24 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ (x45 ≥ 0))) := by
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
  have u4 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1745 t x02 x12 x23 x24 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u6 (And.intro u5 (And.intro u4 (And.intro u1 u2)))))))) h

theorem clause10834 (t x01 x12 x15 x23 x25 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x23) + x25) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
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
  have u3 : ((t + ((-1) * x23) + x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1746 t x01 x12 x15 x23 x25
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u3 (And.intro u5 (And.intro u0 (And.intro u4 u2)))))) h

theorem clause10836 (t x02 x23 x34 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ (x78 ≥ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1754 t x02 x23 x34 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u2 (And.intro u6 (And.intro u5 u3)))))))) h

theorem clause10837 (t x02 x05 x07 x23 x34 x47 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((t + ((-1) * x02) + x05) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((t + x47 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x02) + x05) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th1763 t x02 x05 x07 x23 x34 x47 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u4 (And.intro u5 (And.intro u7 (And.intro u0 (And.intro u6 (And.intro u1 (And.intro u3 u2)))))))))) h

theorem clause10838 (t x01 x05 x12 x15 x17 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x12) + x15) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x15)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + x17 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x12) + x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x17 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th1778 t x01 x05 x12 x15 x17 x57 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u5 (And.intro u7 (And.intro u2 (And.intro u8 (And.intro u0 (And.intro u4 (And.intro u3 u1)))))))))) h

theorem clause10839 (x16 x46 x67 : ℝ) : ((¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x16 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1781 x16 x46 x67
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u1 u2))) h

theorem clause10840 (x03 x13 x36 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ ((x13 + ((-1) * x36)) ≤ (-1))) := by
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
  have u2 : ¬ ((x13 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1783 x03 x13 x36
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause10842 (x27 x67 x78 : ℝ) : ((¬ ((x27 + ((-1) * x67)) ≥ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x27 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x27 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1788 x27 x67 x78
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u1 u2))) h

theorem clause10843 (x06 x16 x56 : ℝ) : ((¬ ((x06 + ((-1) * x16)) ≥ 0)) ∨ ((x06 + ((-1) * x56)) ≥ 0) ∨ (¬ ((x16 + ((-1) * x56)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x06 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x56)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x16 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1791 x06 x16 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause10844 (x56 x67 x68 : ℝ) : (((x56 + ((-1) * x67)) ≤ (-1)) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x68)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x67 + ((-1) * x68)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1792 x56 x67 x68
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause10845 (t x02 x07 x12 x27 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x12) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x07)) ≥ 0)) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x02) + x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x07 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x07)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1796 t x02 x07 x12 x27 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u1 (And.intro u3 u2))))))) h

theorem clause10846 (t x04 x13 x24 x34 x36 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x46)) ≥ 0)) ∨ (¬ (x45 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
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
  have u4 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th1798 t x04 x13 x24 x34 x36 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u8 (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u6 (And.intro u4 (And.intro u3 u7)))))))))) h

theorem clause10847 (x13 x34 x36 : ℝ) : ((¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x36)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1799 x13 x34 x36
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 u0))) h

theorem clause10849 (t x01 x03 x12 x13 x15 x34 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((t + ((-1) * x12) + x15) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
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
  have u3 : ((x12 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x12) + x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1803 t x01 x03 x12 x13 x15 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u1 (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u2 u3)))))))) h

theorem clause10851 (x23 x35 : ℝ) : ((¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th1805 x23 x35
  exact (fun hh => (Or.elim hh (fun hh => hh u1) (fun zz => ((fun hh => hh u0) zz)))) h

theorem clause10852 (x02 x23 x25 : ℝ) : ((¬ ((x23 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x23 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1806 x02 x23 x25
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 u0)))) h

theorem clause10853 (t x02 x23 x34 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0)) := by
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
  have u3 : ((x02 + ((-1) * x23)) ≥ 1) := by
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
  have u6 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1811 t x02 x23 x34 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u6 (And.intro u0 (And.intro u4 (And.intro u1 u3)))))))) h

theorem clause10855 (t x01 x03 x13 x15 x34 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((t + ((-1) * x13) + x15) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
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
  have u4 : ((t + ((-1) * x13) + x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1816 t x01 x03 x13 x15 x34
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u2 (And.intro u3 (And.intro u1 (And.intro u5 u4)))))) h

theorem clause10856 (x01 x06 x17 x67 : ℝ) : (((x06 + ((-1) * x67)) ≥ 1) ∨ (¬ ((x01 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x67)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x17 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th1817 x01 x06 x17 x67
  exact (fun hh => u0 (hh (And.intro u2 (And.intro u1 u3)))) h

theorem clause10858 (x04 x24 x45 : ℝ) : (((x24 + ((-1) * x45)) ≤ (-1)) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1820 x04 x24 x45
  exact (fun hh => u0 (hh (And.intro u2 u1))) h

theorem clause10859 (t x01 x12 x14 x23 x24 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x23) + x24) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x24)) ≥ 0))) := by
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
  have u3 : ((t + ((-1) * x23) + x24) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1822 t x01 x12 x14 x23 x24
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u4 (And.intro u0 (And.intro u5 (And.intro u1 u3))))))) h

theorem clause10860 (t x01 x13 x17 x23 x37 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x13) + x23) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x13) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x17 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1823 t x01 x13 x17 x23 x37
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u4 (And.intro u1 (And.intro u3 u5))))))) h

theorem clause10861 (t x01 x13 x14 x34 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x14 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((t + x34 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x34 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1824 t x01 x13 x14 x34 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u5 u2))))))) h

theorem clause10862 (t x01 x15 x16 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x56) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x16 + ((-1) * x56)) ≤ 0) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1825 t x01 x15 x16 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u1 u5))))))) h

theorem clause10863 (t x02 x04 x05 x23 x36 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((t + ((-1) * x02) + x04) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + x36 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x02) + x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x36 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th1826 t x02 x04 x05 x23 x36 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u6 (And.intro u5 (And.intro u0 (And.intro u7 (And.intro u4 (And.intro u8 u3)))))))))) h

theorem clause10864 (t x04 x05 x12 x13 x14 x23 x36 x37 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x14)) ≥ 0)) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((t + ((-1) * x12) + x14) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1)) ∨ (¬ (x37 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x12) + x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
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
  have u11 : ((x23 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))))
  have u12 : (x37 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))))
  have h := NineTheoryTrial.th1827 t x04 x05 x12 x13 x14 x23 x36 x37 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u9 (And.intro u1 (And.intro u10 (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u5 (And.intro u4 (And.intro u8 (And.intro u7 (And.intro u11 (And.intro u6 u12)))))))))))))) h

theorem clause10865 (t x01 x06 x14 x16 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((t + x14 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x14 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1828 t x01 x06 x14 x16 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u0 (And.intro u4 (And.intro u3 u1))))))) h

theorem clause10866 (t x01 x04 x13 x15 x34 x38 x45 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ (x15 ≥ 0)) ∨ (¬ ((t + x34 + ((-1) * x38)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x38)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
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
  have u6 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x15 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + x34 + ((-1) * x38)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x13 + ((-1) * x38)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th1830 t x01 x04 x13 x15 x34 x38 x45 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u10 (And.intro u8 (And.intro u6 (And.intro u0 (And.intro u7 (And.intro u4 (And.intro u3 (And.intro u5 (And.intro u9 u2)))))))))))) h

theorem clause10880 (t x23 x28 x38 : ℝ) : (((x23 + ((-1) * x38)) ≤ (-1)) ∨ ((x28 + ((-1) * x38)) ≥ 0) ∨ (¬ (x23 ≤ x28)) ∨ (¬ (x28 ≤ x38)) ∨ (¬ ((x38 - x23) ≥ 1)) ∨ (¬ ((x28 - x23) ≤ (t - 1))) ∨ (¬ ((x38 - x28) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x38)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 + ((-1) * x38)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x38 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x28 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x38 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1836 t x23 x28 x38
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause10882 (t x23 x28 x38 : ℝ) : (((x23 + ((-1) * x38)) ≤ (-1)) ∨ ((x23 + ((-1) * x38)) ≥ 1) ∨ (¬ (x23 ≤ x28)) ∨ (¬ (x28 ≤ x38)) ∨ (¬ ((x38 - x23) ≥ 1)) ∨ (¬ ((x28 - x23) ≤ (t - 1))) ∨ (¬ ((x38 - x28) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x38)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x38)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x38 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x28 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x38 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1836 t x23 x28 x38
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause10905 (t x23 x28 x38 : ℝ) : (((x23 + ((-1) * x38)) ≤ (-1)) ∨ ((x28 + ((-1) * x38)) ≥ 0) ∨ (¬ (x38 ≤ x28)) ∨ (¬ (x28 ≤ x23)) ∨ (¬ ((x23 - x38) ≥ 1)) ∨ (¬ ((x23 - x28) ≤ (t - 1))) ∨ (¬ ((x28 - x38) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x38)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 + ((-1) * x38)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x38 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x38) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x28 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1836 t x23 x28 x38
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause10907 (t x23 x28 x38 : ℝ) : (((x23 + ((-1) * x38)) ≤ (-1)) ∨ ((x23 + ((-1) * x38)) ≥ 1) ∨ (¬ (x38 ≤ x28)) ∨ (¬ (x28 ≤ x23)) ∨ (¬ ((x23 - x38) ≥ 1)) ∨ (¬ ((x23 - x28) ≤ (t - 1))) ∨ (¬ ((x28 - x38) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x38)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x38)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x38 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x38) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x28 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1836 t x23 x28 x38
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause10970 (t x23 x28 x38 : ℝ) (h : (((x23 ≤ x28) ∧ (x28 ≤ x38) ∧ ((x38 - x23) ≥ 1) ∧ ((x28 - x23) ≤ (t - 1)) ∧ ((x38 - x28) ≤ (t - 1))) ∨ ((x38 ≤ x28) ∧ (x28 ≤ x23) ∧ ((x23 - x38) ≥ 1) ∧ ((x23 - x28) ≤ (t - 1)) ∧ ((x28 - x38) ≤ (t - 1))))) : ((x23 ≤ x28) ∨ (x38 ≤ x28)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x28) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause10971 (t x23 x28 x38 : ℝ) (h : (((x23 ≤ x28) ∧ (x28 ≤ x38) ∧ ((x38 - x23) ≥ 1) ∧ ((x28 - x23) ≤ (t - 1)) ∧ ((x38 - x28) ≤ (t - 1))) ∨ ((x38 ≤ x28) ∧ (x28 ≤ x23) ∧ ((x23 - x38) ≥ 1) ∧ ((x23 - x28) ≤ (t - 1)) ∧ ((x28 - x38) ≤ (t - 1))))) : ((x23 ≤ x28) ∨ (x28 ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x23) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause10972 (t x23 x28 x38 : ℝ) (h : (((x23 ≤ x28) ∧ (x28 ≤ x38) ∧ ((x38 - x23) ≥ 1) ∧ ((x28 - x23) ≤ (t - 1)) ∧ ((x38 - x28) ≤ (t - 1))) ∨ ((x38 ≤ x28) ∧ (x28 ≤ x23) ∧ ((x23 - x38) ≥ 1) ∧ ((x23 - x28) ≤ (t - 1)) ∧ ((x28 - x38) ≤ (t - 1))))) : ((x23 ≤ x28) ∨ ((x23 - x38) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x38) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause10973 (t x23 x28 x38 : ℝ) (h : (((x23 ≤ x28) ∧ (x28 ≤ x38) ∧ ((x38 - x23) ≥ 1) ∧ ((x28 - x23) ≤ (t - 1)) ∧ ((x38 - x28) ≤ (t - 1))) ∨ ((x38 ≤ x28) ∧ (x28 ≤ x23) ∧ ((x23 - x38) ≥ 1) ∧ ((x23 - x28) ≤ (t - 1)) ∧ ((x28 - x38) ≤ (t - 1))))) : ((x23 ≤ x28) ∨ ((x23 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause10974 (t x23 x28 x38 : ℝ) (h : (((x23 ≤ x28) ∧ (x28 ≤ x38) ∧ ((x38 - x23) ≥ 1) ∧ ((x28 - x23) ≤ (t - 1)) ∧ ((x38 - x28) ≤ (t - 1))) ∨ ((x38 ≤ x28) ∧ (x28 ≤ x23) ∧ ((x23 - x38) ≥ 1) ∧ ((x23 - x28) ≤ (t - 1)) ∧ ((x28 - x38) ≤ (t - 1))))) : ((x23 ≤ x28) ∨ ((x28 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause10975 (t x23 x28 x38 : ℝ) (h : (((x23 ≤ x28) ∧ (x28 ≤ x38) ∧ ((x38 - x23) ≥ 1) ∧ ((x28 - x23) ≤ (t - 1)) ∧ ((x38 - x28) ≤ (t - 1))) ∨ ((x38 ≤ x28) ∧ (x28 ≤ x23) ∧ ((x23 - x38) ≥ 1) ∧ ((x23 - x28) ≤ (t - 1)) ∧ ((x28 - x38) ≤ (t - 1))))) : ((x28 ≤ x38) ∨ (x38 ≤ x28)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x28 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x28) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause10976 (t x23 x28 x38 : ℝ) (h : (((x23 ≤ x28) ∧ (x28 ≤ x38) ∧ ((x38 - x23) ≥ 1) ∧ ((x28 - x23) ≤ (t - 1)) ∧ ((x38 - x28) ≤ (t - 1))) ∨ ((x38 ≤ x28) ∧ (x28 ≤ x23) ∧ ((x23 - x38) ≥ 1) ∧ ((x23 - x28) ≤ (t - 1)) ∧ ((x28 - x38) ≤ (t - 1))))) : ((x28 ≤ x38) ∨ (x28 ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x28 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x23) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause10977 (t x23 x28 x38 : ℝ) (h : (((x23 ≤ x28) ∧ (x28 ≤ x38) ∧ ((x38 - x23) ≥ 1) ∧ ((x28 - x23) ≤ (t - 1)) ∧ ((x38 - x28) ≤ (t - 1))) ∨ ((x38 ≤ x28) ∧ (x28 ≤ x23) ∧ ((x23 - x38) ≥ 1) ∧ ((x23 - x28) ≤ (t - 1)) ∧ ((x28 - x38) ≤ (t - 1))))) : ((x28 ≤ x38) ∨ ((x23 - x38) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x28 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x38) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause10978 (t x23 x28 x38 : ℝ) (h : (((x23 ≤ x28) ∧ (x28 ≤ x38) ∧ ((x38 - x23) ≥ 1) ∧ ((x28 - x23) ≤ (t - 1)) ∧ ((x38 - x28) ≤ (t - 1))) ∨ ((x38 ≤ x28) ∧ (x28 ≤ x23) ∧ ((x23 - x38) ≥ 1) ∧ ((x23 - x28) ≤ (t - 1)) ∧ ((x28 - x38) ≤ (t - 1))))) : ((x28 ≤ x38) ∨ ((x23 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x28 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause10979 (t x23 x28 x38 : ℝ) (h : (((x23 ≤ x28) ∧ (x28 ≤ x38) ∧ ((x38 - x23) ≥ 1) ∧ ((x28 - x23) ≤ (t - 1)) ∧ ((x38 - x28) ≤ (t - 1))) ∨ ((x38 ≤ x28) ∧ (x28 ≤ x23) ∧ ((x23 - x38) ≥ 1) ∧ ((x23 - x28) ≤ (t - 1)) ∧ ((x28 - x38) ≤ (t - 1))))) : ((x28 ≤ x38) ∨ ((x28 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x28 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause10980 (t x23 x28 x38 : ℝ) (h : (((x23 ≤ x28) ∧ (x28 ≤ x38) ∧ ((x38 - x23) ≥ 1) ∧ ((x28 - x23) ≤ (t - 1)) ∧ ((x38 - x28) ≤ (t - 1))) ∨ ((x38 ≤ x28) ∧ (x28 ≤ x23) ∧ ((x23 - x38) ≥ 1) ∧ ((x23 - x28) ≤ (t - 1)) ∧ ((x28 - x38) ≤ (t - 1))))) : (((x38 - x23) ≥ 1) ∨ (x38 ≤ x28)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x23) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x28) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause10981 (t x23 x28 x38 : ℝ) (h : (((x23 ≤ x28) ∧ (x28 ≤ x38) ∧ ((x38 - x23) ≥ 1) ∧ ((x28 - x23) ≤ (t - 1)) ∧ ((x38 - x28) ≤ (t - 1))) ∨ ((x38 ≤ x28) ∧ (x28 ≤ x23) ∧ ((x23 - x38) ≥ 1) ∧ ((x23 - x28) ≤ (t - 1)) ∧ ((x28 - x38) ≤ (t - 1))))) : (((x38 - x23) ≥ 1) ∨ (x28 ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x23) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x23) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause10982 (t x23 x28 x38 : ℝ) (h : (((x23 ≤ x28) ∧ (x28 ≤ x38) ∧ ((x38 - x23) ≥ 1) ∧ ((x28 - x23) ≤ (t - 1)) ∧ ((x38 - x28) ≤ (t - 1))) ∨ ((x38 ≤ x28) ∧ (x28 ≤ x23) ∧ ((x23 - x38) ≥ 1) ∧ ((x23 - x28) ≤ (t - 1)) ∧ ((x28 - x38) ≤ (t - 1))))) : (((x38 - x23) ≥ 1) ∨ ((x23 - x38) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x23) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x38) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause10983 (t x23 x28 x38 : ℝ) (h : (((x23 ≤ x28) ∧ (x28 ≤ x38) ∧ ((x38 - x23) ≥ 1) ∧ ((x28 - x23) ≤ (t - 1)) ∧ ((x38 - x28) ≤ (t - 1))) ∨ ((x38 ≤ x28) ∧ (x28 ≤ x23) ∧ ((x23 - x38) ≥ 1) ∧ ((x23 - x28) ≤ (t - 1)) ∧ ((x28 - x38) ≤ (t - 1))))) : (((x38 - x23) ≥ 1) ∨ ((x23 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x23) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause10984 (t x23 x28 x38 : ℝ) (h : (((x23 ≤ x28) ∧ (x28 ≤ x38) ∧ ((x38 - x23) ≥ 1) ∧ ((x28 - x23) ≤ (t - 1)) ∧ ((x38 - x28) ≤ (t - 1))) ∨ ((x38 ≤ x28) ∧ (x28 ≤ x23) ∧ ((x23 - x38) ≥ 1) ∧ ((x23 - x28) ≤ (t - 1)) ∧ ((x28 - x38) ≤ (t - 1))))) : (((x38 - x23) ≥ 1) ∨ ((x28 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x23) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause10985 (t x23 x28 x38 : ℝ) (h : (((x23 ≤ x28) ∧ (x28 ≤ x38) ∧ ((x38 - x23) ≥ 1) ∧ ((x28 - x23) ≤ (t - 1)) ∧ ((x38 - x28) ≤ (t - 1))) ∨ ((x38 ≤ x28) ∧ (x28 ≤ x23) ∧ ((x23 - x38) ≥ 1) ∧ ((x23 - x28) ≤ (t - 1)) ∧ ((x28 - x38) ≤ (t - 1))))) : (((x28 - x23) ≤ (t - 1)) ∨ (x38 ≤ x28)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x23) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x28) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause10986 (t x23 x28 x38 : ℝ) (h : (((x23 ≤ x28) ∧ (x28 ≤ x38) ∧ ((x38 - x23) ≥ 1) ∧ ((x28 - x23) ≤ (t - 1)) ∧ ((x38 - x28) ≤ (t - 1))) ∨ ((x38 ≤ x28) ∧ (x28 ≤ x23) ∧ ((x23 - x38) ≥ 1) ∧ ((x23 - x28) ≤ (t - 1)) ∧ ((x28 - x38) ≤ (t - 1))))) : (((x28 - x23) ≤ (t - 1)) ∨ (x28 ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x23) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x23) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause10987 (t x23 x28 x38 : ℝ) (h : (((x23 ≤ x28) ∧ (x28 ≤ x38) ∧ ((x38 - x23) ≥ 1) ∧ ((x28 - x23) ≤ (t - 1)) ∧ ((x38 - x28) ≤ (t - 1))) ∨ ((x38 ≤ x28) ∧ (x28 ≤ x23) ∧ ((x23 - x38) ≥ 1) ∧ ((x23 - x28) ≤ (t - 1)) ∧ ((x28 - x38) ≤ (t - 1))))) : (((x28 - x23) ≤ (t - 1)) ∨ ((x23 - x38) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x23) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x38) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause10988 (t x23 x28 x38 : ℝ) (h : (((x23 ≤ x28) ∧ (x28 ≤ x38) ∧ ((x38 - x23) ≥ 1) ∧ ((x28 - x23) ≤ (t - 1)) ∧ ((x38 - x28) ≤ (t - 1))) ∨ ((x38 ≤ x28) ∧ (x28 ≤ x23) ∧ ((x23 - x38) ≥ 1) ∧ ((x23 - x28) ≤ (t - 1)) ∧ ((x28 - x38) ≤ (t - 1))))) : (((x28 - x23) ≤ (t - 1)) ∨ ((x23 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x23) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause10989 (t x23 x28 x38 : ℝ) (h : (((x23 ≤ x28) ∧ (x28 ≤ x38) ∧ ((x38 - x23) ≥ 1) ∧ ((x28 - x23) ≤ (t - 1)) ∧ ((x38 - x28) ≤ (t - 1))) ∨ ((x38 ≤ x28) ∧ (x28 ≤ x23) ∧ ((x23 - x38) ≥ 1) ∧ ((x23 - x28) ≤ (t - 1)) ∧ ((x28 - x38) ≤ (t - 1))))) : (((x28 - x23) ≤ (t - 1)) ∨ ((x28 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x23) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause10990 (t x23 x28 x38 : ℝ) (h : (((x23 ≤ x28) ∧ (x28 ≤ x38) ∧ ((x38 - x23) ≥ 1) ∧ ((x28 - x23) ≤ (t - 1)) ∧ ((x38 - x28) ≤ (t - 1))) ∨ ((x38 ≤ x28) ∧ (x28 ≤ x23) ∧ ((x23 - x38) ≥ 1) ∧ ((x23 - x28) ≤ (t - 1)) ∧ ((x28 - x38) ≤ (t - 1))))) : (((x38 - x28) ≤ (t - 1)) ∨ (x38 ≤ x28)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x28) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x28) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause10991 (t x23 x28 x38 : ℝ) (h : (((x23 ≤ x28) ∧ (x28 ≤ x38) ∧ ((x38 - x23) ≥ 1) ∧ ((x28 - x23) ≤ (t - 1)) ∧ ((x38 - x28) ≤ (t - 1))) ∨ ((x38 ≤ x28) ∧ (x28 ≤ x23) ∧ ((x23 - x38) ≥ 1) ∧ ((x23 - x28) ≤ (t - 1)) ∧ ((x28 - x38) ≤ (t - 1))))) : (((x38 - x28) ≤ (t - 1)) ∨ (x28 ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x28) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x23) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause10992 (t x23 x28 x38 : ℝ) (h : (((x23 ≤ x28) ∧ (x28 ≤ x38) ∧ ((x38 - x23) ≥ 1) ∧ ((x28 - x23) ≤ (t - 1)) ∧ ((x38 - x28) ≤ (t - 1))) ∨ ((x38 ≤ x28) ∧ (x28 ≤ x23) ∧ ((x23 - x38) ≥ 1) ∧ ((x23 - x28) ≤ (t - 1)) ∧ ((x28 - x38) ≤ (t - 1))))) : (((x38 - x28) ≤ (t - 1)) ∨ ((x23 - x38) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x28) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x38) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause10993 (t x23 x28 x38 : ℝ) (h : (((x23 ≤ x28) ∧ (x28 ≤ x38) ∧ ((x38 - x23) ≥ 1) ∧ ((x28 - x23) ≤ (t - 1)) ∧ ((x38 - x28) ≤ (t - 1))) ∨ ((x38 ≤ x28) ∧ (x28 ≤ x23) ∧ ((x23 - x38) ≥ 1) ∧ ((x23 - x28) ≤ (t - 1)) ∧ ((x28 - x38) ≤ (t - 1))))) : (((x38 - x28) ≤ (t - 1)) ∨ ((x23 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x28) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause10994 (t x23 x28 x38 : ℝ) (h : (((x23 ≤ x28) ∧ (x28 ≤ x38) ∧ ((x38 - x23) ≥ 1) ∧ ((x28 - x23) ≤ (t - 1)) ∧ ((x38 - x28) ≤ (t - 1))) ∨ ((x38 ≤ x28) ∧ (x28 ≤ x23) ∧ ((x23 - x38) ≥ 1) ∧ ((x23 - x28) ≤ (t - 1)) ∧ ((x28 - x38) ≤ (t - 1))))) : (((x38 - x28) ≤ (t - 1)) ∨ ((x28 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x28) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause11007 (t x13 x18 x38 : ℝ) : (((x13 + ((-1) * x38)) ≤ (-1)) ∨ ((x13 + ((-1) * x38)) ≥ 1) ∨ (¬ (x13 ≤ x18)) ∨ (¬ (x18 ≤ x38)) ∨ (¬ ((x38 - x13) ≥ 1)) ∨ (¬ ((x18 - x13) ≤ (t - 1))) ∨ (¬ ((x38 - x18) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x38)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x38)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x18) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x18 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x38 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x18 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x38 - x18) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1840 t x13 x18 x38
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause11032 (t x13 x18 x38 : ℝ) : (((x13 + ((-1) * x38)) ≤ (-1)) ∨ ((x13 + ((-1) * x38)) ≥ 1) ∨ (¬ (x38 ≤ x18)) ∨ (¬ (x18 ≤ x13)) ∨ (¬ ((x13 - x38) ≥ 1)) ∨ (¬ ((x13 - x18) ≤ (t - 1))) ∨ (¬ ((x18 - x38) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x38)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x38)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x38 ≤ x18) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x18 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x38) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x18) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x18 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1840 t x13 x18 x38
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause11095 (t x13 x18 x38 : ℝ) (h : (((x13 ≤ x18) ∧ (x18 ≤ x38) ∧ ((x38 - x13) ≥ 1) ∧ ((x18 - x13) ≤ (t - 1)) ∧ ((x38 - x18) ≤ (t - 1))) ∨ ((x38 ≤ x18) ∧ (x18 ≤ x13) ∧ ((x13 - x38) ≥ 1) ∧ ((x13 - x18) ≤ (t - 1)) ∧ ((x18 - x38) ≤ (t - 1))))) : ((x13 ≤ x18) ∨ (x38 ≤ x18)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x18) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause11096 (t x13 x18 x38 : ℝ) (h : (((x13 ≤ x18) ∧ (x18 ≤ x38) ∧ ((x38 - x13) ≥ 1) ∧ ((x18 - x13) ≤ (t - 1)) ∧ ((x38 - x18) ≤ (t - 1))) ∨ ((x38 ≤ x18) ∧ (x18 ≤ x13) ∧ ((x13 - x38) ≥ 1) ∧ ((x13 - x18) ≤ (t - 1)) ∧ ((x18 - x38) ≤ (t - 1))))) : ((x13 ≤ x18) ∨ (x18 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause11097 (t x13 x18 x38 : ℝ) (h : (((x13 ≤ x18) ∧ (x18 ≤ x38) ∧ ((x38 - x13) ≥ 1) ∧ ((x18 - x13) ≤ (t - 1)) ∧ ((x38 - x18) ≤ (t - 1))) ∨ ((x38 ≤ x18) ∧ (x18 ≤ x13) ∧ ((x13 - x38) ≥ 1) ∧ ((x13 - x18) ≤ (t - 1)) ∧ ((x18 - x38) ≤ (t - 1))))) : ((x13 ≤ x18) ∨ ((x13 - x38) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x38) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause11098 (t x13 x18 x38 : ℝ) (h : (((x13 ≤ x18) ∧ (x18 ≤ x38) ∧ ((x38 - x13) ≥ 1) ∧ ((x18 - x13) ≤ (t - 1)) ∧ ((x38 - x18) ≤ (t - 1))) ∨ ((x38 ≤ x18) ∧ (x18 ≤ x13) ∧ ((x13 - x38) ≥ 1) ∧ ((x13 - x18) ≤ (t - 1)) ∧ ((x18 - x38) ≤ (t - 1))))) : ((x13 ≤ x18) ∨ ((x13 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause11099 (t x13 x18 x38 : ℝ) (h : (((x13 ≤ x18) ∧ (x18 ≤ x38) ∧ ((x38 - x13) ≥ 1) ∧ ((x18 - x13) ≤ (t - 1)) ∧ ((x38 - x18) ≤ (t - 1))) ∨ ((x38 ≤ x18) ∧ (x18 ≤ x13) ∧ ((x13 - x38) ≥ 1) ∧ ((x13 - x18) ≤ (t - 1)) ∧ ((x18 - x38) ≤ (t - 1))))) : ((x13 ≤ x18) ∨ ((x18 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause11100 (t x13 x18 x38 : ℝ) (h : (((x13 ≤ x18) ∧ (x18 ≤ x38) ∧ ((x38 - x13) ≥ 1) ∧ ((x18 - x13) ≤ (t - 1)) ∧ ((x38 - x18) ≤ (t - 1))) ∨ ((x38 ≤ x18) ∧ (x18 ≤ x13) ∧ ((x13 - x38) ≥ 1) ∧ ((x13 - x18) ≤ (t - 1)) ∧ ((x18 - x38) ≤ (t - 1))))) : ((x18 ≤ x38) ∨ (x38 ≤ x18)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x18 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x18) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause11101 (t x13 x18 x38 : ℝ) (h : (((x13 ≤ x18) ∧ (x18 ≤ x38) ∧ ((x38 - x13) ≥ 1) ∧ ((x18 - x13) ≤ (t - 1)) ∧ ((x38 - x18) ≤ (t - 1))) ∨ ((x38 ≤ x18) ∧ (x18 ≤ x13) ∧ ((x13 - x38) ≥ 1) ∧ ((x13 - x18) ≤ (t - 1)) ∧ ((x18 - x38) ≤ (t - 1))))) : ((x18 ≤ x38) ∨ (x18 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x18 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause11102 (t x13 x18 x38 : ℝ) (h : (((x13 ≤ x18) ∧ (x18 ≤ x38) ∧ ((x38 - x13) ≥ 1) ∧ ((x18 - x13) ≤ (t - 1)) ∧ ((x38 - x18) ≤ (t - 1))) ∨ ((x38 ≤ x18) ∧ (x18 ≤ x13) ∧ ((x13 - x38) ≥ 1) ∧ ((x13 - x18) ≤ (t - 1)) ∧ ((x18 - x38) ≤ (t - 1))))) : ((x18 ≤ x38) ∨ ((x13 - x38) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x18 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x38) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause11103 (t x13 x18 x38 : ℝ) (h : (((x13 ≤ x18) ∧ (x18 ≤ x38) ∧ ((x38 - x13) ≥ 1) ∧ ((x18 - x13) ≤ (t - 1)) ∧ ((x38 - x18) ≤ (t - 1))) ∨ ((x38 ≤ x18) ∧ (x18 ≤ x13) ∧ ((x13 - x38) ≥ 1) ∧ ((x13 - x18) ≤ (t - 1)) ∧ ((x18 - x38) ≤ (t - 1))))) : ((x18 ≤ x38) ∨ ((x13 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x18 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause11104 (t x13 x18 x38 : ℝ) (h : (((x13 ≤ x18) ∧ (x18 ≤ x38) ∧ ((x38 - x13) ≥ 1) ∧ ((x18 - x13) ≤ (t - 1)) ∧ ((x38 - x18) ≤ (t - 1))) ∨ ((x38 ≤ x18) ∧ (x18 ≤ x13) ∧ ((x13 - x38) ≥ 1) ∧ ((x13 - x18) ≤ (t - 1)) ∧ ((x18 - x38) ≤ (t - 1))))) : ((x18 ≤ x38) ∨ ((x18 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x18 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause11105 (t x13 x18 x38 : ℝ) (h : (((x13 ≤ x18) ∧ (x18 ≤ x38) ∧ ((x38 - x13) ≥ 1) ∧ ((x18 - x13) ≤ (t - 1)) ∧ ((x38 - x18) ≤ (t - 1))) ∨ ((x38 ≤ x18) ∧ (x18 ≤ x13) ∧ ((x13 - x38) ≥ 1) ∧ ((x13 - x18) ≤ (t - 1)) ∧ ((x18 - x38) ≤ (t - 1))))) : (((x38 - x13) ≥ 1) ∨ (x38 ≤ x18)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x13) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x18) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause11106 (t x13 x18 x38 : ℝ) (h : (((x13 ≤ x18) ∧ (x18 ≤ x38) ∧ ((x38 - x13) ≥ 1) ∧ ((x18 - x13) ≤ (t - 1)) ∧ ((x38 - x18) ≤ (t - 1))) ∨ ((x38 ≤ x18) ∧ (x18 ≤ x13) ∧ ((x13 - x38) ≥ 1) ∧ ((x13 - x18) ≤ (t - 1)) ∧ ((x18 - x38) ≤ (t - 1))))) : (((x38 - x13) ≥ 1) ∨ (x18 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x13) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause11107 (t x13 x18 x38 : ℝ) (h : (((x13 ≤ x18) ∧ (x18 ≤ x38) ∧ ((x38 - x13) ≥ 1) ∧ ((x18 - x13) ≤ (t - 1)) ∧ ((x38 - x18) ≤ (t - 1))) ∨ ((x38 ≤ x18) ∧ (x18 ≤ x13) ∧ ((x13 - x38) ≥ 1) ∧ ((x13 - x18) ≤ (t - 1)) ∧ ((x18 - x38) ≤ (t - 1))))) : (((x38 - x13) ≥ 1) ∨ ((x13 - x38) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x13) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x38) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause11108 (t x13 x18 x38 : ℝ) (h : (((x13 ≤ x18) ∧ (x18 ≤ x38) ∧ ((x38 - x13) ≥ 1) ∧ ((x18 - x13) ≤ (t - 1)) ∧ ((x38 - x18) ≤ (t - 1))) ∨ ((x38 ≤ x18) ∧ (x18 ≤ x13) ∧ ((x13 - x38) ≥ 1) ∧ ((x13 - x18) ≤ (t - 1)) ∧ ((x18 - x38) ≤ (t - 1))))) : (((x38 - x13) ≥ 1) ∨ ((x13 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x13) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause11109 (t x13 x18 x38 : ℝ) (h : (((x13 ≤ x18) ∧ (x18 ≤ x38) ∧ ((x38 - x13) ≥ 1) ∧ ((x18 - x13) ≤ (t - 1)) ∧ ((x38 - x18) ≤ (t - 1))) ∨ ((x38 ≤ x18) ∧ (x18 ≤ x13) ∧ ((x13 - x38) ≥ 1) ∧ ((x13 - x18) ≤ (t - 1)) ∧ ((x18 - x38) ≤ (t - 1))))) : (((x38 - x13) ≥ 1) ∨ ((x18 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x13) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause11110 (t x13 x18 x38 : ℝ) (h : (((x13 ≤ x18) ∧ (x18 ≤ x38) ∧ ((x38 - x13) ≥ 1) ∧ ((x18 - x13) ≤ (t - 1)) ∧ ((x38 - x18) ≤ (t - 1))) ∨ ((x38 ≤ x18) ∧ (x18 ≤ x13) ∧ ((x13 - x38) ≥ 1) ∧ ((x13 - x18) ≤ (t - 1)) ∧ ((x18 - x38) ≤ (t - 1))))) : (((x18 - x13) ≤ (t - 1)) ∨ (x38 ≤ x18)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x18) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause11111 (t x13 x18 x38 : ℝ) (h : (((x13 ≤ x18) ∧ (x18 ≤ x38) ∧ ((x38 - x13) ≥ 1) ∧ ((x18 - x13) ≤ (t - 1)) ∧ ((x38 - x18) ≤ (t - 1))) ∨ ((x38 ≤ x18) ∧ (x18 ≤ x13) ∧ ((x13 - x38) ≥ 1) ∧ ((x13 - x18) ≤ (t - 1)) ∧ ((x18 - x38) ≤ (t - 1))))) : (((x18 - x13) ≤ (t - 1)) ∨ (x18 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause11112 (t x13 x18 x38 : ℝ) (h : (((x13 ≤ x18) ∧ (x18 ≤ x38) ∧ ((x38 - x13) ≥ 1) ∧ ((x18 - x13) ≤ (t - 1)) ∧ ((x38 - x18) ≤ (t - 1))) ∨ ((x38 ≤ x18) ∧ (x18 ≤ x13) ∧ ((x13 - x38) ≥ 1) ∧ ((x13 - x18) ≤ (t - 1)) ∧ ((x18 - x38) ≤ (t - 1))))) : (((x18 - x13) ≤ (t - 1)) ∨ ((x13 - x38) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x38) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause11113 (t x13 x18 x38 : ℝ) (h : (((x13 ≤ x18) ∧ (x18 ≤ x38) ∧ ((x38 - x13) ≥ 1) ∧ ((x18 - x13) ≤ (t - 1)) ∧ ((x38 - x18) ≤ (t - 1))) ∨ ((x38 ≤ x18) ∧ (x18 ≤ x13) ∧ ((x13 - x38) ≥ 1) ∧ ((x13 - x18) ≤ (t - 1)) ∧ ((x18 - x38) ≤ (t - 1))))) : (((x18 - x13) ≤ (t - 1)) ∨ ((x13 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause11114 (t x13 x18 x38 : ℝ) (h : (((x13 ≤ x18) ∧ (x18 ≤ x38) ∧ ((x38 - x13) ≥ 1) ∧ ((x18 - x13) ≤ (t - 1)) ∧ ((x38 - x18) ≤ (t - 1))) ∨ ((x38 ≤ x18) ∧ (x18 ≤ x13) ∧ ((x13 - x38) ≥ 1) ∧ ((x13 - x18) ≤ (t - 1)) ∧ ((x18 - x38) ≤ (t - 1))))) : (((x18 - x13) ≤ (t - 1)) ∨ ((x18 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause11115 (t x13 x18 x38 : ℝ) (h : (((x13 ≤ x18) ∧ (x18 ≤ x38) ∧ ((x38 - x13) ≥ 1) ∧ ((x18 - x13) ≤ (t - 1)) ∧ ((x38 - x18) ≤ (t - 1))) ∨ ((x38 ≤ x18) ∧ (x18 ≤ x13) ∧ ((x13 - x38) ≥ 1) ∧ ((x13 - x18) ≤ (t - 1)) ∧ ((x18 - x38) ≤ (t - 1))))) : (((x38 - x18) ≤ (t - 1)) ∨ (x38 ≤ x18)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x18) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x18) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause11116 (t x13 x18 x38 : ℝ) (h : (((x13 ≤ x18) ∧ (x18 ≤ x38) ∧ ((x38 - x13) ≥ 1) ∧ ((x18 - x13) ≤ (t - 1)) ∧ ((x38 - x18) ≤ (t - 1))) ∨ ((x38 ≤ x18) ∧ (x18 ≤ x13) ∧ ((x13 - x38) ≥ 1) ∧ ((x13 - x18) ≤ (t - 1)) ∧ ((x18 - x38) ≤ (t - 1))))) : (((x38 - x18) ≤ (t - 1)) ∨ (x18 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x18) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause11117 (t x13 x18 x38 : ℝ) (h : (((x13 ≤ x18) ∧ (x18 ≤ x38) ∧ ((x38 - x13) ≥ 1) ∧ ((x18 - x13) ≤ (t - 1)) ∧ ((x38 - x18) ≤ (t - 1))) ∨ ((x38 ≤ x18) ∧ (x18 ≤ x13) ∧ ((x13 - x38) ≥ 1) ∧ ((x13 - x18) ≤ (t - 1)) ∧ ((x18 - x38) ≤ (t - 1))))) : (((x38 - x18) ≤ (t - 1)) ∨ ((x13 - x38) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x18) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x38) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause11118 (t x13 x18 x38 : ℝ) (h : (((x13 ≤ x18) ∧ (x18 ≤ x38) ∧ ((x38 - x13) ≥ 1) ∧ ((x18 - x13) ≤ (t - 1)) ∧ ((x38 - x18) ≤ (t - 1))) ∨ ((x38 ≤ x18) ∧ (x18 ≤ x13) ∧ ((x13 - x38) ≥ 1) ∧ ((x13 - x18) ≤ (t - 1)) ∧ ((x18 - x38) ≤ (t - 1))))) : (((x38 - x18) ≤ (t - 1)) ∨ ((x13 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x18) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause11119 (t x13 x18 x38 : ℝ) (h : (((x13 ≤ x18) ∧ (x18 ≤ x38) ∧ ((x38 - x13) ≥ 1) ∧ ((x18 - x13) ≤ (t - 1)) ∧ ((x38 - x18) ≤ (t - 1))) ∨ ((x38 ≤ x18) ∧ (x18 ≤ x13) ∧ ((x13 - x38) ≥ 1) ∧ ((x13 - x18) ≤ (t - 1)) ∧ ((x18 - x38) ≤ (t - 1))))) : (((x38 - x18) ≤ (t - 1)) ∨ ((x18 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x18) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause11120 (t x01 x04 x12 x14 x17 x47 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x12) + x14) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + x17 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x12) + x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 + ((-1) * x78)) ≥ 1) := by
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
  have h := NineTheoryTrial.th1842 t x01 x04 x12 x14 x17 x47 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u6 (And.intro u8 (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u5 u7)))))))))) h

theorem clause11122 (t x01 x16 x17 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x16) + x36) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x67)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x16) + x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1844 t x01 x16 x17 x36 x67
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u5 u4)))))) h

theorem clause11123 (t x02 x23 x36 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1847 t x02 x23 x36 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u6 u4)))))))) h

theorem clause11124 (x04 x34 x45 : ℝ) : ((¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ ((x04 + ((-1) * x45)) ≥ 1) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1851 x04 x34 x45
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause11126 (t x04 x35 x45 x46 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x35 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1))) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1853 t x04 x35 x45 x46 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u0 (And.intro u4 (And.intro u3 u2))))))) h

theorem clause11127 (x04 x34 x47 : ℝ) : ((¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1854 x04 x34 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 u2)))) h

theorem clause11128 (t x02 x03 x23 x34 x37 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
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
  have u3 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1856 t x02 x03 x23 x34 x37 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u7 (And.intro u6 u5))))))))) h

theorem clause11129 (x02 x12 x24 : ℝ) : ((¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ ((x12 + ((-1) * x24)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x12 + ((-1) * x24)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1857 x02 x12 x24
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause11130 (x14 x34 x45 : ℝ) : ((¬ ((x14 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x14 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1860 x14 x34 x45
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u0 u1))) h

theorem clause11131 (t x02 x03 x24 x34 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ (x45 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1864 t x02 x03 x24 x34 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u4 (And.intro u7 (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u3 u5))))))))) h

theorem clause11132 (t x23 x36 x37 x56 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1)) ∨ (¬ (x37 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x37 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1869 t x23 x36 x37 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u4 (And.intro u5 (And.intro u0 (And.intro u3 (And.intro u1 u2)))))))) h

theorem clause11133 (t x13 x34 x36 x46 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ ((t + ((-1) * x13)) ≤ 0) ∨ (¬ ((x34 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ (x67 ≥ 0)) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1870 t x13 x34 x36 x46 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u7 (And.intro u3 (And.intro u4 (And.intro u0 (And.intro u2 u6))))))))) h

theorem clause11134 (t x57 x68 x78 : ℝ) : ((¬ (x68 ≥ 0)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ ((t + ((-1) * x57)) ≤ 0) ∨ ((t + x68 + ((-1) * x78)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (x68 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + x68 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th1872 t x57 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u2 u3))))) h

theorem clause11135 (t x04 x23 x34 x36 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + ((-1) * x04) + x34) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x04) + x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1876 t x04 x23 x34 x36 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u1 u5))))))) h

theorem clause11136 (t x01 x13 x16 x23 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x13) + x23) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x36)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x13) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1883 t x01 x13 x16 x23 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u5 (And.intro u0 (And.intro u4 u2))))))) h

theorem clause11138 (x36 x67 x68 : ℝ) : ((¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x68)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x67 + ((-1) * x68)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1888 x36 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 u0)))) h

theorem clause11139 (t x02 x06 x23 x34 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + x46 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + ((-1) * x02) + x06) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x46)) ≥ 1) := by
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
  have u6 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x02) + x06) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1891 t x02 x06 x23 x34 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u0 (And.intro u6 (And.intro u5 (And.intro u3 (And.intro u2 (And.intro u1 u4))))))))) h

theorem clause11140 (t x02 x03 x23 x34 x35 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ (x57 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x34)) ≥ 1) := by
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
  have u5 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x57 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1892 t x02 x03 x23 x34 x35 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u6 (And.intro u0 (And.intro u7 (And.intro u1 (And.intro u5 (And.intro u2 u3))))))))) h

theorem clause11141 (t x01 x05 x12 x15 x16 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((t + x67 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x12) + x15) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x15)) ≥ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x67 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x16)) ≥ 1) := by
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
  have u6 : ((t + ((-1) * x12) + x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x05 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th1895 t x01 x05 x12 x15 x16 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u7 (And.intro u4 (And.intro u0 (And.intro u8 (And.intro u6 (And.intro u2 u3)))))))))) h

theorem clause11142 (t x01 x03 x12 x13 x17 x34 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x17) ≥ 1))) := by
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
  have u3 : ((x12 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x12) + x17) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1897 t x01 x03 x12 x13 x17 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u6 (And.intro u5 (And.intro u1 (And.intro u4 u0)))))))) h

theorem clause11143 (x02 x03 x23 x24 : ℝ) : ((¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th1898 x02 x03 x23 x24
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u2 u3))))) h

theorem clause11144 (t x01 x04 x12 x14 x17 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x17) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x12) + x17) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1899 t x01 x04 x12 x14 x17 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u6 (And.intro u5 (And.intro u0 (And.intro u3 u4)))))))) h

theorem clause11145 (t x01 x15 x16 x35 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((t + ((-1) * x15) + x35) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x15) + x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1904 t x01 x15 x16 x35 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u3 u1))))))) h

theorem clause11147 (t x13 x23 x35 x36 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ ((t + ((-1) * x13)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x67 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x56)) ≥ 0) := by
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
  have h := NineTheoryTrial.th1907 t x13 x23 x35 x36 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u4 (And.intro u7 (And.intro u5 (And.intro u6 (And.intro u0 u3))))))))) h

theorem clause11148 (t x02 x06 x07 x12 x16 x23 x35 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ ((x02 + ((-1) * x12)) ≥ 0) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x16)) ≥ 0)) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x16) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x02 + ((-1) * x12)) ≥ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x07)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((t + ((-1) * x12) + x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th1909 t x02 x06 x07 x12 x16 x23 x35 x57 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u10 (And.intro u6 (And.intro u3 (And.intro u2 (And.intro u7 (And.intro u0 (And.intro u1 (And.intro u8 (And.intro u5 u9)))))))))))) h

theorem clause11151 (t x02 x23 x35 x56 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ (x68 ≥ 0)) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x68 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1912 t x02 x23 x35 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u1 (And.intro u0 (And.intro u5 (And.intro u3 (And.intro u4 u2)))))))) h

theorem clause11153 (x01 x13 x14 : ℝ) : ((¬ ((x13 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x13 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1922 x01 x13 x14
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u2 u1))) h

theorem clause11154 (x01 x03 x14 x34 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th1923 x01 x03 x14 x34
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u3 (And.intro u2 u0)))) h

theorem clause11155 (t x01 x13 x14 x23 x34 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x14 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((t + ((-1) * x13) + x23) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x13) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1930 t x01 x13 x14 x23 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u4 (And.intro u2 (And.intro u5 u0))))))) h

theorem clause11156 (t x01 x05 x06 x12 x14 x15 x24 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + x46 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((t + ((-1) * x12) + x15) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x15)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x46 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x05 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x12) + x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x05 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th1931 t x01 x05 x06 x12 x14 x15 x24 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u2 (And.intro u7 (And.intro u9 (And.intro u4 (And.intro u10 (And.intro u8 (And.intro u3 u6)))))))))))) h

theorem clause11157 (x04 x14 x45 : ℝ) : (((x04 + ((-1) * x45)) ≥ 1) ∨ (¬ ((x04 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1933 x04 x14 x45
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause11158 (x01 x03 x04 : ℝ) : ((¬ ((x01 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ ((x01 + ((-1) * x04)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x01 + ((-1) * x04)) ≤ 0) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1934 x01 x03 x04
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause11159 (x17 x47 x78 : ℝ) : ((¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x47)) ≥ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x17 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1941 x17 x47 x78
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u0 u2))) h

theorem clause11160 (x05 x57 : ℝ) : ((¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th1944 x05 x57
  exact (fun hh => (Or.elim hh (fun hh => hh u0) (fun zz => ((fun hh => hh u1) zz)))) h

theorem clause11161 (x14 x34 x45 : ℝ) : ((¬ ((x14 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ ((x14 + ((-1) * x45)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x14 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x14 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1959 x14 x34 x45
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause11162 (t x01 x14 x35 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x35 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x35 ≥ 0) := by
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
  have u4 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1960 t x01 x14 x35 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u3 u6)))))))) h

theorem clause11163 (t x01 x12 x16 x23 x26 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((t + ((-1) * x23) + x26) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x26)) ≥ 0))) := by
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
  have u3 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x23) + x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1962 t x01 x12 x16 x23 x26
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u3 (And.intro u5 (And.intro u0 (And.intro u2 u4)))))) h

theorem clause11164 (t x05 x46 x56 : ℝ) : (((t + ((-1) * x46)) ≤ 0) ∨ ((t + ((-1) * x46) + x56) ≥ 1) ∨ (¬ (x05 ≥ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x46) + x56) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x05 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th1963 t x05 x46 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u2 u3))))) h

theorem clause11165 (t x01 x12 x14 x34 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ (x34 ≥ 0)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1965 t x01 x12 x14 x34 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u6 u5)))))))) h

theorem clause11167 (t x01 x04 x07 x12 x14 x15 x47 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x47) + x57) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x14) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x47) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x12) + x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x07)) ≤ 0) := by
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
  have u8 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th1968 t x01 x04 x07 x12 x14 x15 x47 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u8 (And.intro u4 (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u9 (And.intro u1 (And.intro u6 u7))))))))))) h

theorem clause11168 (t x01 x04 x12 x14 x15 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x14) ≥ 1)) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x12) + x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x56) + x57) ≥ 1) := by
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
  have h := NineTheoryTrial.th1969 t x01 x04 x12 x14 x15 x45 x56 x57
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u4 (And.intro u7 (And.intro u6 (And.intro u0 (And.intro u8 (And.intro u5 (And.intro u2 u1))))))))) h

theorem clause11169 (t x01 x04 x13 x14 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x13) + x14) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x13) + x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1972 t x01 x04 x13 x14 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u5 (And.intro u4 u3))))))) h

theorem clause11170 (t x01 x13 x15 x35 x56 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x13)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ (x68 ≥ 0)) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x68 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1974 t x01 x13 x15 x35 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u4 (And.intro u0 (And.intro u7 (And.intro u3 u6))))))))) h

theorem clause11172 (t x01 x04 x05 x12 x14 x16 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((t + x67 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x14) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x67 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x12) + x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th1980 t x01 x04 x05 x12 x14 x16 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u9 (And.intro u8 (And.intro u7 (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u5 (And.intro u4 u6))))))))))) h

theorem clause11173 (t x01 x04 x12 x14 x17 x47 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x12) + x14) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + x17 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x12) + x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x17 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th1983 t x01 x04 x12 x14 x17 x47 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u5 (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u4 (And.intro u7 (And.intro u0 u8)))))))))) h

theorem clause11174 (t x05 x45 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x05 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x05 + ((-1) * x45)) ≥ 1) := by
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
  have u5 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1984 t x05 x45 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u5 (And.intro u4 (And.intro u2 u0))))))) h

theorem clause11176 (x23 x35 x38 : ℝ) : ((¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x38)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x38)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x38)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x38)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1988 x23 x35 x38
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u0 u2))) h

theorem clause11177 (x01 x02 x17 x27 : ℝ) : ((¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x27)) ≥ 0)) ∨ ((x02 + ((-1) * x27)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x02)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x17 + ((-1) * x27)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((x02 + ((-1) * x27)) ≥ 1) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th1992 x01 x02 x17 x27
  exact (fun hh => u3 (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause11178 (t x01 x13 x15 x23 x35 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x13) + x23) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x13) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1996 t x01 x13 x15 x23 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u1 (And.intro u5 (And.intro u0 u3))))))) h

theorem clause11179 (t x02 x14 x24 x45 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≥ 1) := by
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
  have u4 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1997 t x02 x14 x24 x45 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u3 (And.intro u2 u6)))))))) h

theorem clause11182 (x01 x02 x03 : ℝ) : ((¬ ((x01 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x02)) ≥ 0)) ∨ ((x02 + ((-1) * x03)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x02)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x02 + ((-1) * x03)) ≤ 0) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2011 x01 x02 x03
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 u2)))) h

theorem clause11183 (t x34 x36 x45 x46 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((t + x45 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1)))) := by
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
  have u4 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2014 t x34 x36 x45 x46 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u5 (And.intro u4 (And.intro u1 u0))))))) h

theorem clause11184 (x04 x24 x46 : ℝ) : ((¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ ((x04 + ((-1) * x46)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x04 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2017 x04 x24 x46
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause11185 (x07 x37 x78 : ℝ) : (((x07 + ((-1) * x78)) ≥ 1) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x37)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x07 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2019 x07 x37 x78
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause11186 (x17 x47 x67 : ℝ) : ((¬ ((x47 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((x17 + ((-1) * x47)) ≤ 0)) ∨ ((x17 + ((-1) * x67)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x47 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x17 + ((-1) * x47)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x17 + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2020 x17 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 u1)))) h

theorem clause11188 (x04 x14 x45 : ℝ) : ((¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2022 x04 x14 x45
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u1 u2))) h

theorem clause11189 (t x01 x04 x12 x14 x17 x45 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x14) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + x17 + ((-1) * x67)) ≥ 1))) := by
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
  have u3 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x12) + x14) ≥ 1) := by
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
  have h := NineTheoryTrial.th2025 t x01 x04 x12 x14 x17 x45 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u8 (And.intro u7 (And.intro u5 (And.intro u6 (And.intro u1 (And.intro u0 u4)))))))))) h

theorem clause11190 (x67 x78 : ℝ) : ((¬ ((x67 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th2029 x67 x78
  exact (fun hh => (Or.elim hh (fun hh => hh u0) (fun zz => ((fun hh => hh u1) zz)))) h

theorem clause11191 (t x36 x56 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x36 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x57)) ≥ 0)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x36 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2030 t x36 x56 x57 x67 x78
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u2 (And.intro u3 (And.intro u5 (And.intro u0 u4)))))) h

theorem clause11192 (x47 x67 x78 : ℝ) : ((¬ ((x47 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x47 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2031 x47 x67 x78
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u1 u2))) h

theorem clause11194 (t x02 x04 x05 x12 x14 x23 x37 x45 x56 x58 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ ((x02 + ((-1) * x12)) ≥ 0) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x14)) ≥ 0)) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((t + ((-1) * x12) + x14) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x58)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x12)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x12) + x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x45 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x05 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x23 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))))
  have u12 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))))
  have h := NineTheoryTrial.th2034 t x02 x04 x05 x12 x14 x23 x37 x45 x56 x58 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u11 (And.intro u5 (And.intro u0 (And.intro u7 (And.intro u3 (And.intro u1 (And.intro u6 (And.intro u9 (And.intro u8 (And.intro u10 (And.intro u12 (And.intro u2 u4)))))))))))))) h

theorem clause11195 (t x36 x37 x56 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x36 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x37)) ≤ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x36 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x67)) ≥ 1) := by
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
  have h := NineTheoryTrial.th2035 t x36 x37 x56 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u5 u4))))))) h

theorem clause11196 (x06 x16 x36 : ℝ) : (((x06 + ((-1) * x36)) ≥ 0) ∨ (¬ ((x06 + ((-1) * x16)) ≥ 0)) ∨ (¬ ((x16 + ((-1) * x36)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 + ((-1) * x36)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ((x06 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x16 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2036 x06 x16 x36
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause11197 (x06 x36 x68 : ℝ) : ((¬ ((x06 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x06 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x06 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2037 x06 x36 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause11199 (t x01 x05 x12 x35 x56 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x05 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x35 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2044 t x01 x05 x12 x35 x56 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u6 (And.intro u5 (And.intro u3 (And.intro u4 (And.intro u7 u1))))))))) h

theorem clause11201 (t x04 x05 x45 x46 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((t + ((-1) * x45) + x46) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x58)) ≤ (-1)))) := by
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
  have u4 : ((x45 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2046 t x04 x05 x45 x46 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u1 (And.intro u5 (And.intro u2 u3))))))) h

theorem clause11202 (t x01 x06 x07 x12 x14 x16 x47 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x16)) ≥ 0)) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x57)) ≥ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x16) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x07)) ≤ 0) := by
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
  have u5 : ((x06 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x47 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((t + ((-1) * x12) + x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th2047 t x01 x06 x07 x12 x14 x16 x47 x57 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u2 (And.intro u0 (And.intro u6 (And.intro u5 (And.intro u10 (And.intro u3 (And.intro u8 (And.intro u9 u7)))))))))))) h

theorem clause11203 (t x05 x07 x45 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x05 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x05 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x05 + ((-1) * x07)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2053 t x05 x07 x45 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u5 u4))))))) h

theorem clause11204 (t x05 x45 x47 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x05 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x47)) ≥ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x05 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th2054 t x05 x45 x47 x57 x78
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 (And.intro u5 (And.intro u4 (And.intro u3 u0)))))) h

theorem clause11208 (t x01 x14 x15 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x45) + x46) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x45) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x46)) ≥ 1) := by
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
  have h := NineTheoryTrial.th2060 t x01 x14 x15 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u4 (And.intro u1 (And.intro u0 (And.intro u3 u5))))))) h

theorem clause11209 (t x01 x12 x17 x35 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x57)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x56)) ≥ 1) := by
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
  have u7 : ((x17 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2061 t x01 x12 x17 x35 x56 x57
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u1 (And.intro u2 (And.intro u3 (And.intro u6 (And.intro u0 (And.intro u4 u7)))))))) h

theorem clause11210 (t x01 x13 x16 x35 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x35) + x36) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x36)) ≥ 0))) := by
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
  have u3 : ((t + ((-1) * x35) + x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2062 t x01 x13 x16 x35 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u5 (And.intro u1 u3))))))) h

theorem clause11211 (t x01 x03 x12 x13 x14 x35 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x14) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x12) + x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2063 t x01 x03 x12 x13 x14 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u6 (And.intro u4 (And.intro u2 (And.intro u1 u3)))))))) h

theorem clause11212 (x14 x24 x47 : ℝ) : (((x24 + ((-1) * x47)) ≤ (-1)) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x24)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2064 x14 x24 x47
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause11213 (t x13 x34 x35 x45 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x45) + x47) ≥ 1))) := by
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
  have u3 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x45) + x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2066 t x13 x34 x35 x45 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u5 (And.intro u1 (And.intro u4 u2))))))) h

theorem clause11214 (t x03 x23 x34 x35 x47 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ (x47 ≥ 0)) ∨ ((t + ((-1) * x03)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x03)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2067 t x03 x23 x34 x35 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u6 u2)))))))) h

theorem clause11215 (t x04 x34 x35 x45 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + ((-1) * x04) + x34) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1)))) := by
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
  have u4 : ((x45 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2078 t x04 x34 x35 x45 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u4 u5))))))) h

theorem clause11216 (t x04 x13 x14 x23 x34 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((t + ((-1) * x13) + x23) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x13) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2079 t x04 x13 x14 x23 x34 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u3 (And.intro u6 (And.intro u4 (And.intro u0 u2)))))))) h

theorem clause11217 (x16 x56 x67 : ℝ) : ((¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x16 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2083 x16 x56 x67
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 u0))) h

theorem clause11218 (x24 x34 x46 : ℝ) : ((¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x34)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2085 x24 x34 x46
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 u0))) h

theorem clause11219 (t x02 x23 x24 x34 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((t + ((-1) * x34) + x36) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x34) + x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2086 t x02 x23 x24 x34 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u3 u5))))))) h

theorem clause11220 (t x01 x03 x12 x13 x16 x35 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x16) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x12) + x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2087 t x01 x03 x12 x13 x16 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u4 (And.intro u0 (And.intro u2 (And.intro u5 (And.intro u1 u3)))))))) h

theorem clause11221 (t x13 x23 x24 x34 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + ((-1) * x13) + x23) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x13) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x45)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2090 t x13 x23 x24 x34 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u3 (And.intro u2 u4))))))) h

theorem clause11225 (t x23 x35 x37 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x57)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x56) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2098 t x23 x35 x37 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u4 (And.intro u0 (And.intro u2 u5))))))) h

theorem clause11226 (t x02 x23 x24 x34 x37 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((t + ((-1) * x34) + x37) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x34) + x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2099 t x02 x23 x24 x34 x37
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u1 u2))))))) h

theorem clause11227 (t x01 x13 x17 x34 x37 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((t + ((-1) * x34) + x37) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1))) := by
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
  have u3 : ((x17 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x34) + x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2101 t x01 x13 x17 x34 x37
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u3 u4)))))) h

theorem clause11228 (t x02 x23 x35 x36 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ (x36 ≥ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x67)) ≥ 0)) ∨ ((t + ((-1) * x02)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
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
  have u4 : (x36 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2104 t x02 x23 x35 x36 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u5 (And.intro u4 u6))))))))) h

theorem clause11229 (x15 x45 x56 : ℝ) : (((x45 + ((-1) * x56)) ≥ 1) ∨ (¬ ((x15 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x15 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2107 x15 x45 x56
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause11230 (t x03 x35 x36 x45 x56 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + x35 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x56)) ≤ 0))) := by
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
  have u3 : ((t + x35 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2109 t x03 x35 x36 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u1 u5))))))) h

theorem clause11231 (t x02 x03 x23 x35 x36 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ (¬ (x57 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x57 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2110 t x02 x03 x23 x35 x36 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u7 (And.intro u1 (And.intro u4 (And.intro u3 u6))))))))) h

theorem clause11232 (t x01 x14 x15 x34 x45 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x14 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((t + ((-1) * x45) + x47) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x45) + x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2114 t x01 x14 x15 x34 x45 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u0 (And.intro u2 (And.intro u1 (And.intro u6 u4)))))))) h

theorem clause11233 (t x02 x07 x23 x35 x47 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + ((-1) * x47) + x57) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x02) + x07) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
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
  have u3 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x02) + x07) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2118 t x02 x07 x23 x35 x47 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u5 (And.intro u4 (And.intro u7 u1))))))))) h

theorem clause11234 (t x01 x12 x17 x23 x35 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ ((t + ((-1) * x35)) ≤ 0) ∨ (¬ (x17 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1))) := by
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
  have u4 : ¬ ((t + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x17 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2121 t x01 x12 x17 x23 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u6 (And.intro u5 u3)))))))) h

theorem clause11235 (x02 x03 x25 x35 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ ((x02 + ((-1) * x25)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x25 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((x02 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th2123 x02 x03 x25 x35
  exact (fun hh => u3 (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause11237 (x03 x13 x35 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ ((x13 + ((-1) * x35)) ≥ 1) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2128 x03 x13 x35
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause11238 (t x02 x03 x07 x23 x35 x37 x47 x78 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((t + x37 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((t + ((-1) * x02) + x07) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x37 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x02) + x07) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th2129 t x02 x03 x07 x23 x35 x37 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u8 (And.intro u2 (And.intro u6 (And.intro u3 (And.intro u5 (And.intro u7 u4)))))))))) h

theorem clause11239 (t x02 x24 x27 x46 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x24 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ ((t + ((-1) * x46)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x47)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1)))) := by
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
  have u4 : ((x46 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x27 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2130 t x02 x24 x27 x46 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u6 (And.intro u4 (And.intro u7 (And.intro u0 u5))))))))) h

theorem clause11240 (t x01 x04 x12 x14 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x14) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x12) + x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2131 t x01 x04 x12 x14 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u2 u4))))))) h

theorem clause11241 (t x02 x13 x23 x26 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x13) + x23) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x13) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x36)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2133 t x02 x13 x23 x26 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u3 u4))))))) h

theorem clause11243 (x13 x37 : ℝ) : ((¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th2141 x13 x37
  exact (fun hh => (Or.elim hh (fun hh => hh u1) (fun zz => ((fun hh => hh u0) zz)))) h

theorem clause11244 (x03 x36 x37 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x36 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2143 x03 x36 x37
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 u1)))) h

theorem clause11247 (x03 x13 x37 : ℝ) : ((¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1))) ∨ ((x03 + ((-1) * x37)) ≤ (-1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x03 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2148 x03 x13 x37
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause11248 (t x03 x35 x37 x57 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ (x03 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ ((t + ((-1) * x37) + x57) ≥ 1) ∨ ((t + ((-1) * x37)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x03 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x37) + x57) ≥ 1) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x37)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr hh))))
  have h := NineTheoryTrial.th2149 t x03 x35 x37 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u2 u4)))))) h

theorem clause11249 (x03 x13 x36 x37 : ℝ) : ((¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x36 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th2152 x03 x13 x36 x37
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u0 (And.intro u3 u1)))) h

theorem clause11250 (t x13 x23 x36 x37 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2153 t x13 x23 x36 x37 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u4 (And.intro u6 (And.intro u7 (And.intro u1 (And.intro u3 u2))))))))) h

theorem clause11251 (x03 x13 x37 : ℝ) : ((¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2154 x03 x13 x37
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u0 u2))) h

theorem clause11252 (x13 x23 x35 : ℝ) : ((¬ ((x13 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ ((x13 + ((-1) * x35)) ≤ (-1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x13 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x13 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2158 x13 x23 x35
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause11254 (x13 x23 x36 : ℝ) : ((¬ ((x13 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1)))) := by
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
  have u2 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2161 x13 x23 x36
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u0 u1))) h

theorem clause11255 (t x02 x23 x26 x34 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x34) + x36) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x36)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x34) + x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2162 t x02 x23 x26 x34 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u4 u2))))))) h

theorem clause11256 (t x02 x12 x23 x26 x34 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ (x02 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2163 t x02 x12 x23 x26 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u6 (And.intro u2 (And.intro u4 (And.intro u3 u1)))))))) h

theorem clause11258 (x13 x36 : ℝ) : ((¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th2165 x13 x36
  exact (fun hh => (Or.elim hh (fun hh => hh u1) (fun zz => ((fun hh => hh u0) zz)))) h

theorem clause11259 (x13 x23 x36 x37 : ℝ) : ((¬ ((x13 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x37)) ≥ 0))) := by
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
  have u2 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th2166 x13 x23 x36 x37
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u1 (And.intro u2 u0)))) h

theorem clause11261 (t x01 x16 x23 x26 x34 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x26 + ((-1) * x68)) ≥ 1)) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x16 + ((-1) * x68)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x16 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2169 t x01 x16 x23 x26 x34 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u5 (And.intro u6 (And.intro u1 (And.intro u7 u4))))))))) h

theorem clause11262 (t x01 x12 x26 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2170 t x01 x12 x26 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u6 (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u3 u2)))))))) h

theorem clause11263 (t x01 x12 x23 x34 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ ((t + ((-1) * x47)) ≤ 0)) := by
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
  have u3 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
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
  have u6 : ¬ ((t + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2171 t x01 x12 x23 x34 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u6 u5)))))))) h

theorem clause11265 (x03 x37 : ℝ) : ((¬ ((x03 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th2175 x03 x37
  exact (fun hh => (Or.elim hh (fun hh => hh u1) (fun zz => ((fun hh => hh u0) zz)))) h

theorem clause11266 (t x02 x12 x23 x27 x35 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ (x02 ≥ 0)) ∨ ((t + ((-1) * x35)) ≤ 0) ∨ (¬ ((x12 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x27)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2176 t x02 x12 x23 x27 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u2 (And.intro u3 u4)))))))) h

theorem clause11267 (t x01 x12 x27 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
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
  have h := NineTheoryTrial.th2177 t x01 x12 x27 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u6 (And.intro u0 (And.intro u3 (And.intro u5 (And.intro u2 u4)))))))) h

theorem clause11269 (t x01 x04 x12 x26 x47 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x04)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x01 + ((-1) * x04)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x68) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2179 t x01 x04 x12 x26 x47 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u4 (And.intro u2 (And.intro u1 (And.intro u6 (And.intro u3 u7))))))))) h

theorem clause11270 (t x01 x04 x14 : ℝ) : (((t + x01 + ((-1) * x04)) ≥ 1) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ ((t + ((-1) * x04)) ≤ 0) ∨ (¬ (x14 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x01 + ((-1) * x04)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x04)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th2180 t x01 x04 x14
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u1 u0))))) h

theorem clause11271 (x13 x14 x23 x34 : ℝ) : ((¬ ((x14 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x14 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th2181 x13 x14 x23 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u0 u1))))) h

theorem clause11272 (t x13 x36 x37 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x67) + x68) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x37 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x67) + x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2182 t x13 x36 x37 x67 x68
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u0 u4)))))) h

theorem clause11273 (x13 x36 x37 : ℝ) : ((¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x36 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2183 x13 x36 x37
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u2 u0))) h

theorem clause11274 (x13 x23 x37 : ℝ) : ((¬ ((x13 + ((-1) * x23)) ≥ 0)) ∨ ((x13 + ((-1) * x37)) ≥ 1) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x13 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2185 x13 x23 x37
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause11275 (x23 x34 : ℝ) : ((¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th2187 x23 x34
  exact (fun hh => (Or.elim hh (fun hh => hh u0) (fun zz => ((fun hh => hh u1) zz)))) h

theorem clause11276 (t x01 x12 x23 x24 x34 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x24)) ≤ 0)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ (x01 ≥ 0))) := by
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
  have u3 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2189 t x01 x12 x23 x24 x34 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u7 (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u6 (And.intro u4 u3))))))))) h

theorem clause11277 (t x01 x12 x23 x34 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ ((t + ((-1) * x46)) ≤ 0) ∨ (¬ (x01 ≥ 0))) := by
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
  have u3 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2190 t x01 x12 x23 x34 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u4 (And.intro u6 u5)))))))) h

theorem clause11278 (t x01 x14 x24 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x46)) ≤ 0) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ (x01 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
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
  have h := NineTheoryTrial.th2192 t x01 x14 x24 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u6 (And.intro u4 (And.intro u2 (And.intro u5 u3)))))))) h

theorem clause11279 (t x01 x12 x14 x24 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ ((t + ((-1) * x24)) ≤ 0) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ (x12 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2193 t x01 x12 x14 x24 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u4 (And.intro u5 (And.intro u0 (And.intro u6 u1)))))))) h

theorem clause11280 (t x24 x34 x35 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((t + ((-1) * x24) + x34) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1))) := by
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
  have u3 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2195 t x24 x34 x35 x45 x56
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u4 u1)))))) h

theorem clause11281 (t x01 x13 x23 x34 x37 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2196 t x01 x13 x23 x34 x37
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u6 (And.intro u4 (And.intro u2 (And.intro u3 u0)))))))) h

theorem clause11282 (t x01 x02 x12 x14 x23 x24 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ ((t + ((-1) * x24)) ≤ 0) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x14)) ≤ 0)) ∨ (¬ (x01 ≥ 0))) := by
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
  have u4 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
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
  have u8 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th2198 t x01 x02 x12 x14 x23 x24 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u4 (And.intro u3 (And.intro u6 (And.intro u0 (And.intro u2 (And.intro u5 (And.intro u1 u7)))))))))) h

theorem clause11283 (t x02 x23 x24 x34 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ ((t + ((-1) * x24)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ (x02 ≥ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2199 t x02 x23 x24 x34 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u6 (And.intro u0 (And.intro u5 u4)))))))) h

theorem clause11284 (x04 x14 x45 : ℝ) : (((x04 + ((-1) * x45)) ≤ (-1)) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2200 x04 x14 x45
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause11285 (t x01 x02 x12 x23 x25 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ (x01 ≥ 0))) := by
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
  have u3 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2204 t x01 x02 x12 x23 x25 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u6 (And.intro u4 (And.intro u7 (And.intro u2 (And.intro u3 u1))))))))) h

theorem clause11286 (t x01 x12 x23 x35 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ (x01 ≥ 0))) := by
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
  have u4 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2205 t x01 x12 x23 x35 x56
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u3 (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u6 u4))))))) h

theorem clause11287 (t x01 x12 x25 x35 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x35)) ≤ 0) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ (x01 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
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
  have h := NineTheoryTrial.th2206 t x01 x12 x25 x35 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u5 (And.intro u1 (And.intro u6 (And.intro u2 u3)))))))) h

theorem clause11288 (t x04 x24 x25 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x04 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1))) := by
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
  have u4 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2208 t x04 x24 x25 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u3 u4))))))) h

theorem clause11289 (x34 x35 x36 : ℝ) : ((¬ ((x34 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x36)) ≤ 0)) ∨ ((x35 + ((-1) * x36)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x35 + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2210 x34 x35 x36
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u0 u2))) h

theorem clause11290 (x04 x14 x46 : ℝ) : ((¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2213 x04 x14 x46
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u1 u2))) h

theorem clause11291 (x14 x45 : ℝ) : ((¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th2214 x14 x45
  exact (fun hh => (Or.elim hh (fun hh => hh u1) (fun zz => ((fun hh => hh u0) zz)))) h

theorem clause11292 (t x02 x03 x23 x24 x34 x36 x47 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x03)) ≤ 0)) ∨ (¬ (x02 ≥ 0)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ ((t + ((-1) * x36)) ≤ 0) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th2216 t x02 x03 x23 x24 x34 x36 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u1 (And.intro u5 (And.intro u6 (And.intro u8 (And.intro u0 (And.intro u7 u2)))))))))) h

theorem clause11293 (x24 x34 x47 : ℝ) : ((¬ ((x24 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x24 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2217 x24 x34 x47
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u1 u2))) h

theorem clause11294 (t x13 x14 x24 x34 x37 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((x24 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x34) + x37) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x34) + x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2218 t x13 x14 x24 x34 x37 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u2 (And.intro u0 u6)))))))) h

theorem clause11295 (t x04 x06 x24 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + x04 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1))) := by
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
  have u4 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2223 t x04 x06 x24 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u4 (And.intro u1 u5))))))) h

theorem clause11297 (t x01 x03 x14 x23 x24 x34 x36 x46 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((t + ((-1) * x24) + x34) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ (x01 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x24) + x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
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
  have u9 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th2233 t x01 x03 x14 x23 x24 x34 x36 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u1 (And.intro u9 (And.intro u6 (And.intro u8 (And.intro u7 (And.intro u0 (And.intro u3 u5))))))))))) h

theorem clause11298 (t x04 x23 x34 : ℝ) : (((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ ((t + x04 + ((-1) * x34)) ≥ 1) ∨ (¬ (x04 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + x04 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th2234 t x04 x23 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u1 u0))))) h

theorem clause11299 (t x03 x24 x34 x35 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + ((-1) * x24) + x34) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1))) := by
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
  have u3 : ((t + ((-1) * x24) + x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2235 t x03 x24 x34 x35 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u1 u4))))))) h

theorem clause11300 (x04 x14 x45 : ℝ) : ((¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2239 x04 x14 x45
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u1 u2))) h

theorem clause11302 (t x01 x03 x14 x36 x45 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x57) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2244 t x01 x03 x14 x36 x45 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u6 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u5 (And.intro u7 u4))))))))) h

theorem clause11303 (t x01 x14 x45 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ (x01 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
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
  have h := NineTheoryTrial.th2245 t x01 x14 x45 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u6 (And.intro u0 (And.intro u4 u5)))))))) h

theorem clause11304 (t x01 x03 x12 x25 x35 x36 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
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
  have u4 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x36)) ≤ 0) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th2248 t x01 x03 x12 x25 x35 x36 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u3 (And.intro u1 (And.intro u7 (And.intro u8 (And.intro u6 u4)))))))))) h

theorem clause11305 (t x02 x24 x25 x34 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x24) + x34) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x45)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
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
  have u4 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2250 t x02 x24 x25 x34 x45
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u5 u4)))))) h

theorem clause11306 (t x01 x03 x14 x35 x45 x56 x57 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1)))) := by
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
  have u3 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th2252 t x01 x03 x14 x35 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u1 (And.intro u4 (And.intro u2 (And.intro u7 (And.intro u5 (And.intro u3 u0))))))))) h

theorem clause11307 (t x01 x03 x14 x35 x46 x57 x67 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1))) := by
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
  have u4 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
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
  have u7 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2253 t x01 x03 x14 x35 x46 x57 x67
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u3 (And.intro u6 (And.intro u4 (And.intro u5 (And.intro u7 (And.intro u0 u1)))))))) h

theorem clause11308 (x04 x14 x46 : ℝ) : (((x04 + ((-1) * x46)) ≤ (-1)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2254 x04 x14 x46
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause11309 (t x01 x03 x12 x26 x35 x57 x67 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
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
  have u4 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
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
  have u7 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2264 t x01 x03 x12 x26 x35 x57 x67
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u0 (And.intro u2 (And.intro u5 (And.intro u7 (And.intro u1 (And.intro u3 u4)))))))) h

theorem clause11310 (t x12 x14 x23 x24 x26 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x23) + x26) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x45)) ≥ 1) := by
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
  have u5 : ((t + ((-1) * x23) + x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2265 t x12 x14 x23 x24 x26 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u2 (And.intro u3 (And.intro u6 (And.intro u1 u0)))))))) h

theorem clause11311 (x06 x67 : ℝ) : ((¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th2268 x06 x67
  exact (fun hh => (Or.elim hh (fun hh => hh u0) (fun zz => ((fun hh => hh u1) zz)))) h

theorem clause11312 (x07 : ℝ) (h : (x07 ≥ 0)) : ((x07 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause11313 (x04 x34 x46 : ℝ) : ((¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ ((x04 + ((-1) * x46)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x04 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2271 x04 x34 x46
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause11314 (t x04 x26 x46 x47 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((t + ((-1) * x26) + x46) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x47 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x26) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2272 t x04 x26 x46 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u2 (And.intro u3 (And.intro u0 u1))))))) h

theorem clause11317 (x47 x57 x78 : ℝ) : ((¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ ((x57 + ((-1) * x78)) ≤ (-1)) ∨ (¬ ((x47 + ((-1) * x57)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x57 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x47 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2277 x47 x57 x78
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause11318 (x01 x12 x16 : ℝ) : ((¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((x01 + ((-1) * x16)) ≤ (-1)) ∨ (¬ ((x12 + ((-1) * x16)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x16)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2287 x01 x12 x16
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause11319 (x12 x26 : ℝ) : ((¬ ((x12 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th2288 x12 x26
  exact (fun hh => (Or.elim hh (fun hh => hh u0) (fun zz => ((fun hh => hh u1) zz)))) h

theorem clause11320 (t x01 x13 x23 x35 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ ((t + ((-1) * x35)) ≤ 0) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2293 t x01 x13 x23 x35 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u4 (And.intro u3 (And.intro u0 (And.intro u5 (And.intro u6 u1)))))))) h

theorem clause11321 (t x13 x14 x24 x34 x36 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((x24 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + ((-1) * x34) + x36) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x45)) ≥ 1) := by
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
  have h := NineTheoryTrial.th2294 t x13 x14 x24 x34 x36 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u6 (And.intro u4 (And.intro u5 (And.intro u3 (And.intro u1 u2)))))))) h

theorem clause11322 (x07 x67 x78 : ℝ) : ((¬ ((x07 + ((-1) * x67)) ≥ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x07 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2300 x07 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 u1)))) h

theorem clause11323 (t x03 x06 x13 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x03 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x03 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x36)) ≥ 1) := by
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
  have h := NineTheoryTrial.th2301 t x03 x06 x13 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u5 (And.intro u0 (And.intro u2 u3))))))) h

theorem clause11324 (t x07 x13 x34 x37 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ (x07 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x37)) ≥ 1) := by
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
  have u6 : (x07 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2304 t x07 x13 x34 x37 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u5 (And.intro u0 u4)))))))) h

theorem clause11326 (t x01 x12 x13 x23 x27 x34 x36 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((t + x68 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x23)) ≤ 0) := by
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
  have u4 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x27)) ≤ (-1)) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x27 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th2306 t x01 x12 x13 x23 x27 x34 x36 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u7 (And.intro u4 (And.intro u0 (And.intro u6 (And.intro u3 (And.intro u5 (And.intro u10 (And.intro u8 (And.intro u9 u2)))))))))))) h

theorem clause11327 (t x01 x17 x23 x27 x34 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x27)) ≥ 0)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 + ((-1) * x27)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2307 t x01 x17 x23 x27 x34 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u6 (And.intro u4 (And.intro u7 (And.intro u0 (And.intro u5 u2))))))))) h

theorem clause11328 (t x01 x06 x12 x13 x23 x26 x34 x36 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + x67 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((x26 + ((-1) * x68)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x23)) ≤ 0) := by
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
  have u4 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x67 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x06 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x26 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th2309 t x01 x06 x12 x13 x23 x26 x34 x36 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u9 (And.intro u7 (And.intro u11 (And.intro u10 (And.intro u1 (And.intro u2 (And.intro u5 (And.intro u0 (And.intro u3 (And.intro u8 (And.intro u4 u6))))))))))))) h

theorem clause11329 (t x07 x35 x37 x45 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x35) + x45) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x07 + ((-1) * x57)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x35) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x07 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2315 t x07 x35 x37 x45 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u6 (And.intro u2 (And.intro u5 (And.intro u1 u0)))))))) h

theorem clause11330 (t x13 x16 x34 x36 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x34) + x36) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x16)) ≥ 0)) ∨ (¬ ((x16 + ((-1) * x68)) ≥ 1))) := by
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
  have u3 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2319 t x13 x16 x34 x36 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u3 (And.intro u4 (And.intro u5 u0))))))) h

theorem clause11331 (x13 x23 x36 : ℝ) : ((¬ ((x13 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ ((x23 + ((-1) * x36)) ≥ 1)) := by
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
  have u2 : ¬ ((x23 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2325 x13 x23 x36
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause11332 (t x23 x35 x36 x56 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x56)) ≥ 0)) ∨ ((t + ((-1) * x35)) ≤ 0) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
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
  have u4 : ¬ ((t + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x67)) ≥ 1) := by
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
  have h := NineTheoryTrial.th2326 t x23 x35 x36 x56 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u2 (And.intro u1 (And.intro u3 (And.intro u5 (And.intro u7 u6))))))))) h

theorem clause11333 (x23 x35 x36 : ℝ) : ((¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x36)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2327 x23 x35 x36
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 u0))) h

theorem clause11334 (x12 x23 x24 : ℝ) : ((¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x24)) ≤ 0)) ∨ ((x12 + ((-1) * x24)) ≤ (-1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x12 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x12 + ((-1) * x24)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2331 x12 x23 x24
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause11335 (t x12 x13 x23 x24 x37 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + x23 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x23 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2333 t x12 x13 x23 x24 x37
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u2 (And.intro u0 (And.intro u1 u5))))))) h

theorem clause11336 (x13 x15 x36 x56 : ℝ) : ((¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x15)) ≤ 0)) ∨ ((x15 + ((-1) * x56)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x36 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((x15 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th2335 x13 x15 x36 x56
  exact (fun hh => u3 (hh (And.intro u1 (And.intro u2 u0)))) h

theorem clause11337 (x13 x23 x35 : ℝ) : ((¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2336 x13 x23 x35
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u2 u1))) h

theorem clause11338 (t x01 x05 x12 x26 x57 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x05)) ≥ 1)) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x26 + ((-1) * x68)) ≤ (-1)) := by
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
  have u6 : ((t + ((-1) * x68) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2342 t x01 x05 x12 x26 x57 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u5 (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u1 (And.intro u4 u6))))))))) h

theorem clause11339 (t x01 x05 x15 : ℝ) : (((t + ((-1) * x05)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ ((t + x01 + ((-1) * x05)) ≥ 1) ∨ (¬ (x15 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x05)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + x01 + ((-1) * x05)) ≥ 1) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th2347 t x01 x05 x15
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u1 u2))))) h

theorem clause11340 (x13 x23 x37 : ℝ) : ((¬ ((x13 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x13 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2351 x13 x23 x37
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u2 u0))) h

theorem clause11341 (x02 x03 x07 : ℝ) : ((¬ ((x02 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x07)) ≤ 0)) ∨ ((x02 + ((-1) * x07)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x07)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x02 + ((-1) * x07)) ≤ 0) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2352 x02 x03 x07
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause11342 (t x13 x23 x34 x37 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x67 ≥ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 + ((-1) * x78)) ≥ 1) := by
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
  have h := NineTheoryTrial.th2358 t x13 x23 x34 x37 x67 x78
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u6 (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u7 u4)))))))) h

theorem clause11343 (x13 x36 x37 : ℝ) : ((¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ ((x13 + ((-1) * x37)) ≥ 1) ∨ (¬ ((x36 + ((-1) * x37)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x36 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2359 x13 x36 x37
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause11345 (t x01 x03 x13 x17 x27 x36 x78 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x17)) ≤ 0)) ∨ (¬ (x01 ≥ 0)) ∨ ((t + ((-1) * x27)) ≤ 0) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
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
  have u3 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x17)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th2365 t x01 x03 x13 x17 x27 x36 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u1 (And.intro u2 (And.intro u4 (And.intro u0 (And.intro u6 (And.intro u7 (And.intro u5 u3)))))))))) h

theorem clause11346 (x17 x37 x78 : ℝ) : ((¬ ((x17 + ((-1) * x37)) ≤ 0)) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x17 + ((-1) * x37)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2367 x17 x37 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 u1)))) h

theorem clause11347 (t x01 x03 x04 x13 x36 x37 x45 x57 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x04)) ≥ 1)) ∨ (¬ ((t + ((-1) * x37) + x57) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1)))) := by
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
  have u3 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x36)) ≥ 1) := by
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
  have h := NineTheoryTrial.th2371 t x01 x03 x04 x13 x36 x37 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u0 (And.intro u4 (And.intro u7 (And.intro u5 (And.intro u6 (And.intro u3 (And.intro u1 u2)))))))))) h

theorem clause11348 (t x03 x04 x13 x17 x34 x36 x47 x78 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((t + x04 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ (x03 ≥ 0)) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ ((t + ((-1) * x17)) ≤ 0)) := by
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
  have u3 : ((t + x04 + ((-1) * x34)) ≥ 1) := by
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
  have u6 : (x03 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ¬ ((t + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th2372 t x03 x04 x13 x17 x34 x36 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u8 (And.intro u0 (And.intro u4 (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u3 (And.intro u7 u9))))))))))) h

theorem clause11349 (t x04 x07 x34 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((t + x04 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x04 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x07)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2373 t x04 x07 x34 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u4 (And.intro u3 (And.intro u0 (And.intro u5 u1))))))) h

theorem clause11350 (t x01 x03 x04 x13 x14 x36 x37 x45 x47 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1))) ∨ ((t + ((-1) * x14)) ≤ 0) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((t + ((-1) * x37) + x47) ≥ 1))) := by
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
  have u3 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x13 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x14)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((t + ((-1) * x37) + x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th2374 t x01 x03 x04 x13 x14 x36 x37 x45 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u9 (And.intro u0 (And.intro u4 (And.intro u6 (And.intro u2 (And.intro u1 (And.intro u7 (And.intro u8 (And.intro u5 (And.intro u3 u10)))))))))))) h

theorem clause11353 (t x02 x03 x12 x23 x37 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((t + x02 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1))) := by
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
  have u3 : ((x02 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2378 t x02 x03 x12 x23 x37
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u4 (And.intro u5 u3))))))) h

theorem clause11354 (t x01 x13 x23 x34 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ (x36 ≥ 0)) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0)) := by
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
  have u3 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x36 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2379 t x01 x13 x23 x34 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u6 (And.intro u5 (And.intro u3 (And.intro u2 u1)))))))) h

theorem clause11355 (x13 x34 x37 : ℝ) : ((¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x37)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2380 x13 x34 x37
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u0 u1))) h

theorem clause11356 (t x02 x13 x23 x24 x34 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + ((-1) * x13) + x23) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x13) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2383 t x02 x13 x23 x24 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u1 u4))))))) h

theorem clause11357 (t x04 x13 x14 x23 x34 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((t + ((-1) * x13) + x23) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x13) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
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
  have u6 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2387 t x04 x13 x14 x23 x34 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u4 (And.intro u6 (And.intro u0 u5)))))))) h

theorem clause11358 (x23 x36 : ℝ) : ((¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th2390 x23 x36
  exact (fun hh => (Or.elim hh (fun hh => hh u1) (fun zz => ((fun hh => hh u0) zz)))) h

theorem clause11359 (x03 x34 x36 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2391 x03 x34 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 u0)))) h

theorem clause11360 (x03 x35 x37 : ℝ) : (((x03 + ((-1) * x35)) ≤ (-1)) ∨ (¬ ((x35 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2392 x03 x35 x37
  exact (fun hh => u0 (hh (And.intro u2 u1))) h

theorem clause11361 (t x02 x03 x23 x25 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x23 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x23 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2394 t x02 x03 x23 x25 x36
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u3 u5)))))) h

theorem clause11362 (x03 x35 x37 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1)))) := by
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
  have u2 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2397 x03 x35 x37
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u2 u1))) h

theorem clause11363 (x02 x03 x05 : ℝ) : ((¬ ((x02 + ((-1) * x03)) ≤ 0)) ∨ ((x02 + ((-1) * x05)) ≤ 0) ∨ (¬ ((x03 + ((-1) * x05)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x05)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2398 x02 x03 x05
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 u2)))) h

theorem clause11364 (t x04 x13 x34 x35 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x45) + x46) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1))) := by
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
  have u3 : ((x04 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x45) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2399 t x04 x13 x34 x35 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u6 (And.intro u5 (And.intro u1 (And.intro u2 u0)))))))) h

theorem clause11365 (t x03 x23 x36 x37 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x57)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2401 t x03 x23 x36 x37 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u7 (And.intro u2 (And.intro u6 u5))))))))) h

theorem clause11380 (t x02 x08 x28 : ℝ) : (((x02 + ((-1) * x28)) ≤ (-1)) ∨ ((x02 + ((-1) * x28)) ≥ 1) ∨ (¬ (x02 ≤ x08)) ∨ (¬ (x08 ≤ x28)) ∨ (¬ ((x28 - x02) ≥ 1)) ∨ (¬ ((x08 - x02) ≤ (t - 1))) ∨ (¬ ((x28 - x08) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x28)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x28)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x08) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x08 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x28 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x08 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x28 - x08) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2413 t x02 x08 x28
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause11405 (t x02 x08 x28 : ℝ) : (((x02 + ((-1) * x28)) ≤ (-1)) ∨ ((x02 + ((-1) * x28)) ≥ 1) ∨ (¬ (x28 ≤ x08)) ∨ (¬ (x08 ≤ x02)) ∨ (¬ ((x02 - x28) ≥ 1)) ∨ (¬ ((x02 - x08) ≤ (t - 1))) ∨ (¬ ((x08 - x28) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x28)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x28)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x28 ≤ x08) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x08 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x28) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x08) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x08 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2413 t x02 x08 x28
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause11468 (t x02 x08 x28 : ℝ) (h : (((x02 ≤ x08) ∧ (x08 ≤ x28) ∧ ((x28 - x02) ≥ 1) ∧ ((x08 - x02) ≤ (t - 1)) ∧ ((x28 - x08) ≤ (t - 1))) ∨ ((x28 ≤ x08) ∧ (x08 ≤ x02) ∧ ((x02 - x28) ≥ 1) ∧ ((x02 - x08) ≤ (t - 1)) ∧ ((x08 - x28) ≤ (t - 1))))) : ((x02 ≤ x08) ∨ (x28 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause11469 (t x02 x08 x28 : ℝ) (h : (((x02 ≤ x08) ∧ (x08 ≤ x28) ∧ ((x28 - x02) ≥ 1) ∧ ((x08 - x02) ≤ (t - 1)) ∧ ((x28 - x08) ≤ (t - 1))) ∨ ((x28 ≤ x08) ∧ (x08 ≤ x02) ∧ ((x02 - x28) ≥ 1) ∧ ((x02 - x08) ≤ (t - 1)) ∧ ((x08 - x28) ≤ (t - 1))))) : ((x02 ≤ x08) ∨ (x08 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause11470 (t x02 x08 x28 : ℝ) (h : (((x02 ≤ x08) ∧ (x08 ≤ x28) ∧ ((x28 - x02) ≥ 1) ∧ ((x08 - x02) ≤ (t - 1)) ∧ ((x28 - x08) ≤ (t - 1))) ∨ ((x28 ≤ x08) ∧ (x08 ≤ x02) ∧ ((x02 - x28) ≥ 1) ∧ ((x02 - x08) ≤ (t - 1)) ∧ ((x08 - x28) ≤ (t - 1))))) : ((x02 ≤ x08) ∨ ((x02 - x28) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x28) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause11471 (t x02 x08 x28 : ℝ) (h : (((x02 ≤ x08) ∧ (x08 ≤ x28) ∧ ((x28 - x02) ≥ 1) ∧ ((x08 - x02) ≤ (t - 1)) ∧ ((x28 - x08) ≤ (t - 1))) ∨ ((x28 ≤ x08) ∧ (x08 ≤ x02) ∧ ((x02 - x28) ≥ 1) ∧ ((x02 - x08) ≤ (t - 1)) ∧ ((x08 - x28) ≤ (t - 1))))) : ((x02 ≤ x08) ∨ ((x02 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause11472 (t x02 x08 x28 : ℝ) (h : (((x02 ≤ x08) ∧ (x08 ≤ x28) ∧ ((x28 - x02) ≥ 1) ∧ ((x08 - x02) ≤ (t - 1)) ∧ ((x28 - x08) ≤ (t - 1))) ∨ ((x28 ≤ x08) ∧ (x08 ≤ x02) ∧ ((x02 - x28) ≥ 1) ∧ ((x02 - x08) ≤ (t - 1)) ∧ ((x08 - x28) ≤ (t - 1))))) : ((x02 ≤ x08) ∨ ((x08 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause11473 (t x02 x08 x28 : ℝ) (h : (((x02 ≤ x08) ∧ (x08 ≤ x28) ∧ ((x28 - x02) ≥ 1) ∧ ((x08 - x02) ≤ (t - 1)) ∧ ((x28 - x08) ≤ (t - 1))) ∨ ((x28 ≤ x08) ∧ (x08 ≤ x02) ∧ ((x02 - x28) ≥ 1) ∧ ((x02 - x08) ≤ (t - 1)) ∧ ((x08 - x28) ≤ (t - 1))))) : ((x08 ≤ x28) ∨ (x28 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause11474 (t x02 x08 x28 : ℝ) (h : (((x02 ≤ x08) ∧ (x08 ≤ x28) ∧ ((x28 - x02) ≥ 1) ∧ ((x08 - x02) ≤ (t - 1)) ∧ ((x28 - x08) ≤ (t - 1))) ∨ ((x28 ≤ x08) ∧ (x08 ≤ x02) ∧ ((x02 - x28) ≥ 1) ∧ ((x02 - x08) ≤ (t - 1)) ∧ ((x08 - x28) ≤ (t - 1))))) : ((x08 ≤ x28) ∨ (x08 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause11475 (t x02 x08 x28 : ℝ) (h : (((x02 ≤ x08) ∧ (x08 ≤ x28) ∧ ((x28 - x02) ≥ 1) ∧ ((x08 - x02) ≤ (t - 1)) ∧ ((x28 - x08) ≤ (t - 1))) ∨ ((x28 ≤ x08) ∧ (x08 ≤ x02) ∧ ((x02 - x28) ≥ 1) ∧ ((x02 - x08) ≤ (t - 1)) ∧ ((x08 - x28) ≤ (t - 1))))) : ((x08 ≤ x28) ∨ ((x02 - x28) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x28) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause11476 (t x02 x08 x28 : ℝ) (h : (((x02 ≤ x08) ∧ (x08 ≤ x28) ∧ ((x28 - x02) ≥ 1) ∧ ((x08 - x02) ≤ (t - 1)) ∧ ((x28 - x08) ≤ (t - 1))) ∨ ((x28 ≤ x08) ∧ (x08 ≤ x02) ∧ ((x02 - x28) ≥ 1) ∧ ((x02 - x08) ≤ (t - 1)) ∧ ((x08 - x28) ≤ (t - 1))))) : ((x08 ≤ x28) ∨ ((x02 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause11477 (t x02 x08 x28 : ℝ) (h : (((x02 ≤ x08) ∧ (x08 ≤ x28) ∧ ((x28 - x02) ≥ 1) ∧ ((x08 - x02) ≤ (t - 1)) ∧ ((x28 - x08) ≤ (t - 1))) ∨ ((x28 ≤ x08) ∧ (x08 ≤ x02) ∧ ((x02 - x28) ≥ 1) ∧ ((x02 - x08) ≤ (t - 1)) ∧ ((x08 - x28) ≤ (t - 1))))) : ((x08 ≤ x28) ∨ ((x08 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause11478 (t x02 x08 x28 : ℝ) (h : (((x02 ≤ x08) ∧ (x08 ≤ x28) ∧ ((x28 - x02) ≥ 1) ∧ ((x08 - x02) ≤ (t - 1)) ∧ ((x28 - x08) ≤ (t - 1))) ∨ ((x28 ≤ x08) ∧ (x08 ≤ x02) ∧ ((x02 - x28) ≥ 1) ∧ ((x02 - x08) ≤ (t - 1)) ∧ ((x08 - x28) ≤ (t - 1))))) : (((x28 - x02) ≥ 1) ∨ (x28 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause11479 (t x02 x08 x28 : ℝ) (h : (((x02 ≤ x08) ∧ (x08 ≤ x28) ∧ ((x28 - x02) ≥ 1) ∧ ((x08 - x02) ≤ (t - 1)) ∧ ((x28 - x08) ≤ (t - 1))) ∨ ((x28 ≤ x08) ∧ (x08 ≤ x02) ∧ ((x02 - x28) ≥ 1) ∧ ((x02 - x08) ≤ (t - 1)) ∧ ((x08 - x28) ≤ (t - 1))))) : (((x28 - x02) ≥ 1) ∨ (x08 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause11480 (t x02 x08 x28 : ℝ) (h : (((x02 ≤ x08) ∧ (x08 ≤ x28) ∧ ((x28 - x02) ≥ 1) ∧ ((x08 - x02) ≤ (t - 1)) ∧ ((x28 - x08) ≤ (t - 1))) ∨ ((x28 ≤ x08) ∧ (x08 ≤ x02) ∧ ((x02 - x28) ≥ 1) ∧ ((x02 - x08) ≤ (t - 1)) ∧ ((x08 - x28) ≤ (t - 1))))) : (((x28 - x02) ≥ 1) ∨ ((x02 - x28) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x28) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause11481 (t x02 x08 x28 : ℝ) (h : (((x02 ≤ x08) ∧ (x08 ≤ x28) ∧ ((x28 - x02) ≥ 1) ∧ ((x08 - x02) ≤ (t - 1)) ∧ ((x28 - x08) ≤ (t - 1))) ∨ ((x28 ≤ x08) ∧ (x08 ≤ x02) ∧ ((x02 - x28) ≥ 1) ∧ ((x02 - x08) ≤ (t - 1)) ∧ ((x08 - x28) ≤ (t - 1))))) : (((x28 - x02) ≥ 1) ∨ ((x02 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause11482 (t x02 x08 x28 : ℝ) (h : (((x02 ≤ x08) ∧ (x08 ≤ x28) ∧ ((x28 - x02) ≥ 1) ∧ ((x08 - x02) ≤ (t - 1)) ∧ ((x28 - x08) ≤ (t - 1))) ∨ ((x28 ≤ x08) ∧ (x08 ≤ x02) ∧ ((x02 - x28) ≥ 1) ∧ ((x02 - x08) ≤ (t - 1)) ∧ ((x08 - x28) ≤ (t - 1))))) : (((x28 - x02) ≥ 1) ∨ ((x08 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause11483 (t x02 x08 x28 : ℝ) (h : (((x02 ≤ x08) ∧ (x08 ≤ x28) ∧ ((x28 - x02) ≥ 1) ∧ ((x08 - x02) ≤ (t - 1)) ∧ ((x28 - x08) ≤ (t - 1))) ∨ ((x28 ≤ x08) ∧ (x08 ≤ x02) ∧ ((x02 - x28) ≥ 1) ∧ ((x02 - x08) ≤ (t - 1)) ∧ ((x08 - x28) ≤ (t - 1))))) : (((x08 - x02) ≤ (t - 1)) ∨ (x28 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause11484 (t x02 x08 x28 : ℝ) (h : (((x02 ≤ x08) ∧ (x08 ≤ x28) ∧ ((x28 - x02) ≥ 1) ∧ ((x08 - x02) ≤ (t - 1)) ∧ ((x28 - x08) ≤ (t - 1))) ∨ ((x28 ≤ x08) ∧ (x08 ≤ x02) ∧ ((x02 - x28) ≥ 1) ∧ ((x02 - x08) ≤ (t - 1)) ∧ ((x08 - x28) ≤ (t - 1))))) : (((x08 - x02) ≤ (t - 1)) ∨ (x08 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause11485 (t x02 x08 x28 : ℝ) (h : (((x02 ≤ x08) ∧ (x08 ≤ x28) ∧ ((x28 - x02) ≥ 1) ∧ ((x08 - x02) ≤ (t - 1)) ∧ ((x28 - x08) ≤ (t - 1))) ∨ ((x28 ≤ x08) ∧ (x08 ≤ x02) ∧ ((x02 - x28) ≥ 1) ∧ ((x02 - x08) ≤ (t - 1)) ∧ ((x08 - x28) ≤ (t - 1))))) : (((x08 - x02) ≤ (t - 1)) ∨ ((x02 - x28) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x28) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause11486 (t x02 x08 x28 : ℝ) (h : (((x02 ≤ x08) ∧ (x08 ≤ x28) ∧ ((x28 - x02) ≥ 1) ∧ ((x08 - x02) ≤ (t - 1)) ∧ ((x28 - x08) ≤ (t - 1))) ∨ ((x28 ≤ x08) ∧ (x08 ≤ x02) ∧ ((x02 - x28) ≥ 1) ∧ ((x02 - x08) ≤ (t - 1)) ∧ ((x08 - x28) ≤ (t - 1))))) : (((x08 - x02) ≤ (t - 1)) ∨ ((x02 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause11487 (t x02 x08 x28 : ℝ) (h : (((x02 ≤ x08) ∧ (x08 ≤ x28) ∧ ((x28 - x02) ≥ 1) ∧ ((x08 - x02) ≤ (t - 1)) ∧ ((x28 - x08) ≤ (t - 1))) ∨ ((x28 ≤ x08) ∧ (x08 ≤ x02) ∧ ((x02 - x28) ≥ 1) ∧ ((x02 - x08) ≤ (t - 1)) ∧ ((x08 - x28) ≤ (t - 1))))) : (((x08 - x02) ≤ (t - 1)) ∨ ((x08 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause11488 (t x02 x08 x28 : ℝ) (h : (((x02 ≤ x08) ∧ (x08 ≤ x28) ∧ ((x28 - x02) ≥ 1) ∧ ((x08 - x02) ≤ (t - 1)) ∧ ((x28 - x08) ≤ (t - 1))) ∨ ((x28 ≤ x08) ∧ (x08 ≤ x02) ∧ ((x02 - x28) ≥ 1) ∧ ((x02 - x08) ≤ (t - 1)) ∧ ((x08 - x28) ≤ (t - 1))))) : (((x28 - x08) ≤ (t - 1)) ∨ (x28 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause11489 (t x02 x08 x28 : ℝ) (h : (((x02 ≤ x08) ∧ (x08 ≤ x28) ∧ ((x28 - x02) ≥ 1) ∧ ((x08 - x02) ≤ (t - 1)) ∧ ((x28 - x08) ≤ (t - 1))) ∨ ((x28 ≤ x08) ∧ (x08 ≤ x02) ∧ ((x02 - x28) ≥ 1) ∧ ((x02 - x08) ≤ (t - 1)) ∧ ((x08 - x28) ≤ (t - 1))))) : (((x28 - x08) ≤ (t - 1)) ∨ (x08 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause11490 (t x02 x08 x28 : ℝ) (h : (((x02 ≤ x08) ∧ (x08 ≤ x28) ∧ ((x28 - x02) ≥ 1) ∧ ((x08 - x02) ≤ (t - 1)) ∧ ((x28 - x08) ≤ (t - 1))) ∨ ((x28 ≤ x08) ∧ (x08 ≤ x02) ∧ ((x02 - x28) ≥ 1) ∧ ((x02 - x08) ≤ (t - 1)) ∧ ((x08 - x28) ≤ (t - 1))))) : (((x28 - x08) ≤ (t - 1)) ∨ ((x02 - x28) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x28) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause11491 (t x02 x08 x28 : ℝ) (h : (((x02 ≤ x08) ∧ (x08 ≤ x28) ∧ ((x28 - x02) ≥ 1) ∧ ((x08 - x02) ≤ (t - 1)) ∧ ((x28 - x08) ≤ (t - 1))) ∨ ((x28 ≤ x08) ∧ (x08 ≤ x02) ∧ ((x02 - x28) ≥ 1) ∧ ((x02 - x08) ≤ (t - 1)) ∧ ((x08 - x28) ≤ (t - 1))))) : (((x28 - x08) ≤ (t - 1)) ∨ ((x02 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause11492 (t x02 x08 x28 : ℝ) (h : (((x02 ≤ x08) ∧ (x08 ≤ x28) ∧ ((x28 - x02) ≥ 1) ∧ ((x08 - x02) ≤ (t - 1)) ∧ ((x28 - x08) ≤ (t - 1))) ∨ ((x28 ≤ x08) ∧ (x08 ≤ x02) ∧ ((x02 - x28) ≥ 1) ∧ ((x02 - x08) ≤ (t - 1)) ∧ ((x08 - x28) ≤ (t - 1))))) : (((x28 - x08) ≤ (t - 1)) ∨ ((x08 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause11493 (x02 x12 x26 : ℝ) : ((¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2416 x02 x12 x26
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 u1)))) h

theorem clause11494 (t x13 x16 x23 x36 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x13) + x23) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x16)) ≥ 0)) ∨ (¬ ((x16 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x13) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2420 t x13 x16 x23 x36 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u5 u0))))))) h

theorem clause11495 (t x01 x15 x16 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x16)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x16 + ((-1) * x68)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x16 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2422 t x01 x15 x16 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u6 (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u2 (And.intro u3 u7))))))))) h

theorem clause11496 (t x01 x02 x15 x27 x56 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th2427 t x01 x02 x15 x27 x56 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u7 (And.intro u4 (And.intro u2 (And.intro u3 (And.intro u5 u6))))))))) h

theorem clause11497 (t x01 x07 x15 x27 x56 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x27 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ ((t + x01 + ((-1) * x07)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x07 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x27 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x01 + ((-1) * x07)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x27 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2428 t x01 x07 x15 x27 x56 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u1 (And.intro u7 u6))))))))) h

theorem clause11498 (t x03 x35 x37 x56 x57 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x57)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x37)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x56 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2429 t x03 x35 x37 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u3 (And.intro u4 (And.intro u2 u0))))))) h

theorem clause11499 (t x03 x23 x34 x35 x36 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ (x35 ≥ 0)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x35 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2431 t x03 x23 x34 x35 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u6 (And.intro u3 u2)))))))) h

theorem clause11500 (t x02 x03 x23 x34 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x67 ≥ 0))) := by
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
  have u3 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2434 t x02 x03 x23 x34 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u3 (And.intro u7 u6))))))))) h

theorem clause11501 (t x02 x03 x05 x06 x15 x16 x23 x34 x36 x56 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((t + ((-1) * x02) + x05) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + x36 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x16)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x16)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x15)) ≤ 0))) := by
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
  have u3 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x02) + x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x36 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x06 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x06 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x15 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x05 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th2437 t x02 x03 x05 x06 x15 x16 x23 x34 x36 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u9 (And.intro u3 (And.intro u0 (And.intro u5 (And.intro u6 (And.intro u4 (And.intro u11 (And.intro u10 (And.intro u7 u8))))))))))))) h

theorem clause11502 (t x23 x36 x37 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + x36 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x67)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x36 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2438 t x23 x36 x37 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u4 (And.intro u3 u5))))))) h

theorem clause11503 (t x06 x25 x56 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((t + ((-1) * x06) + x56) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1)))) := by
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
  have u4 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2443 t x06 x25 x56 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u5 u4))))))) h

theorem clause11504 (t x01 x02 x03 x12 x15 x16 x23 x34 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x12) + x15) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((t + ((-1) * x16) + x36) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x12) + x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x16) + x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th2444 t x01 x02 x03 x12 x15 x16 x23 x34 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u6 (And.intro u4 (And.intro u9 (And.intro u8 (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u3 u7))))))))))) h

theorem clause11505 (x23 x35 x36 : ℝ) : (((x23 + ((-1) * x35)) ≥ 1) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x36)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2446 x23 x35 x36
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause11507 (x23 x34 x35 x36 : ℝ) : ((¬ ((x34 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x36)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th2450 x23 x34 x35 x36
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u3 (And.intro u1 u2)))) h

theorem clause11509 (t x01 x02 x03 x15 x23 x34 x36 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + x36 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x36 + ((-1) * x56)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th2452 t x01 x02 x03 x15 x23 x34 x36 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u8 (And.intro u0 (And.intro u7 (And.intro u6 (And.intro u5 (And.intro u4 u2)))))))))) h

theorem clause11510 (t x03 x04 x23 x34 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x03) + x23) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x03) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2453 t x03 x04 x23 x34 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u1 (And.intro u5 (And.intro u4 u3))))))) h

theorem clause11511 (t x15 x23 x35 x37 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x15) + x35) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x57)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x15) + x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2454 t x15 x23 x35 x37 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u5 (And.intro u4 u0))))))) h

theorem clause11512 (t x05 x56 x57 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x67) + x68) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
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
  have u4 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x67) + x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2455 t x05 x56 x57 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u5 u4))))))) h

theorem clause11513 (t x01 x02 x16 x27 x47 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((t + x47 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x47 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th2456 t x01 x02 x16 x27 x47 x67 x78
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u6 (And.intro u7 (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u5 u4)))))))) h

theorem clause11515 (t x16 x35 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x35 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x35 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th2459 t x16 x35 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u6 (And.intro u4 (And.intro u5 (And.intro u3 (And.intro u2 u0)))))))) h

theorem clause11516 (t x01 x03 x15 x23 x34 x37 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((t + x37 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1))) := by
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
  have u3 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x37 + ((-1) * x57)) ≥ 1) := by
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
  have u7 : ((x23 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2462 t x01 x03 x15 x23 x34 x37 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u6 (And.intro u3 (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u7 u4))))))))) h

theorem clause11517 (x23 x34 x36 : ℝ) : ((¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2465 x23 x34 x36
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u2 u0))) h

theorem clause11518 (t x01 x03 x16 x34 x45 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x03)) ≥ 1) := by
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
  have u4 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2466 t x01 x03 x16 x34 x45 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u6 (And.intro u7 (And.intro u5 (And.intro u3 (And.intro u4 u2))))))))) h

theorem clause11519 (t x01 x03 x15 x34 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x03)) ≥ 1) := by
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
  have h := NineTheoryTrial.th2467 t x01 x03 x15 x34 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u6 (And.intro u4 (And.intro u7 (And.intro u5 u2))))))))) h

theorem clause11520 (t x23 x36 x37 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x36 ≥ 0)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x36 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x36)) ≥ 1) := by
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
  have h := NineTheoryTrial.th2469 t x23 x36 x37 x67 x78
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u2 (And.intro u4 (And.intro u5 (And.intro u0 (And.intro u1 u3))))))) h

theorem clause11521 (t x13 x14 x15 x23 x35 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((t + ((-1) * x13) + x23) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x15)) ≥ 0)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x13) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2472 t x13 x14 x15 x23 x35 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u6 (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u4 u1)))))))) h

theorem clause11523 (t x01 x02 x12 x16 x17 x24 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x17) + x57) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x16) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≤ 0) := by
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
  have u4 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x17) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x12) + x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th2475 t x01 x02 x12 x16 x17 x24 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u7 (And.intro u6 (And.intro u4 (And.intro u5 (And.intro u1 (And.intro u2 (And.intro u8 u3)))))))))) h

theorem clause11524 (t x01 x02 x03 x06 x16 x23 x34 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((t + ((-1) * x16) + x36) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x16) + x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th2476 t x01 x02 x03 x06 x16 x23 x34 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u9 (And.intro u4 (And.intro u3 (And.intro u6 (And.intro u8 (And.intro u1 (And.intro u5 u7))))))))))) h

theorem clause11525 (t x13 x23 x34 x36 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ ((t + ((-1) * x13)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ (x67 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
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
  have u6 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2478 t x13 x23 x34 x36 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u1 (And.intro u3 (And.intro u6 (And.intro u0 (And.intro u5 u7))))))))) h

theorem clause11527 (x23 x34 x35 : ℝ) : ((¬ ((x34 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2486 x23 x34 x35
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u1 u2))) h

theorem clause11528 (t x04 x13 x14 x23 x34 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((t + ((-1) * x13) + x23) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x13) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2487 t x04 x13 x14 x23 x34 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u6 (And.intro u3 (And.intro u4 (And.intro u5 u1)))))))) h

theorem clause11529 (t x01 x02 x12 x15 x17 x27 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((t + ((-1) * x17) + x47) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x12) + x15) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x17) + x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x12) + x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th2490 t x01 x02 x12 x15 x17 x27 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u2 (And.intro u8 (And.intro u7 u6)))))))))) h

theorem clause11530 (t x02 x03 x05 x34 x47 x56 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((t + ((-1) * x02) + x05) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
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
  have u3 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x02) + x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x68) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th2491 t x02 x03 x05 x34 x47 x56 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u4 (And.intro u5 (And.intro u6 (And.intro u8 (And.intro u7 u3)))))))))) h

theorem clause11531 (t x02 x03 x05 x06 x12 x15 x23 x36 x37 x56 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + x36 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x15) ≥ 1)) ∨ ((x05 + ((-1) * x15)) ≤ 0) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x36 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x05 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x12) + x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ¬ ((x05 + ((-1) * x15)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x03 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th2492 t x02 x03 x05 x06 x12 x15 x23 x36 x37 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u11 (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u10 (And.intro u3 (And.intro u1 (And.intro u9 (And.intro u8 u6))))))))))))) h

theorem clause11532 (t x02 x03 x06 x23 x34 x36 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + x36 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + ((-1) * x02) + x06) ≥ 1))) := by
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
  have u3 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x36 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x02) + x06) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th2495 t x02 x03 x06 x23 x34 x36 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u8 (And.intro u7 (And.intro u0 (And.intro u4 (And.intro u1 (And.intro u6 (And.intro u2 u5)))))))))) h

theorem clause11533 (t x02 x03 x23 x34 x35 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0)) := by
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
  have u3 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2496 t x02 x03 x23 x34 x35 x56
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u3 (And.intro u5 (And.intro u4 (And.intro u7 (And.intro u0 (And.intro u2 u1)))))))) h

theorem clause11534 (t x02 x06 x12 x16 x24 x45 x58 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x58 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x16)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x12) + x16) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≤ 0) := by
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
  have u4 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x58 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x45 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x12) + x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th2501 t x02 x06 x12 x16 x24 x45 x58 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u8 (And.intro u4 (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u9 (And.intro u6 (And.intro u2 u5))))))))))) h

theorem clause11538 (t x02 x03 x05 x23 x34 x37 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x02) + x05) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + x37 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1))) := by
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
  have u3 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x02) + x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x37 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x23 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th2506 t x02 x03 x05 x23 x34 x37 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u7 (And.intro u2 (And.intro u8 (And.intro u0 (And.intro u6 (And.intro u3 u5)))))))))) h

theorem clause11539 (t x01 x02 x14 x23 x37 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((t + x37 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1))) := by
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
  have u3 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
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
  have u6 : ((t + x37 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x23 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2507 t x01 x02 x14 x23 x37 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u6 (And.intro u5 (And.intro u0 (And.intro u7 (And.intro u3 u4))))))))) h

theorem clause11540 (t x01 x02 x03 x16 x23 x34 x37 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((t + x37 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x37 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x23 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th2508 t x01 x02 x03 x16 x23 x34 x37 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u6 (And.intro u7 (And.intro u4 (And.intro u3 (And.intro u5 (And.intro u2 u8)))))))))) h

theorem clause11542 (t x01 x02 x17 x24 x45 x58 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x58 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
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
  have u5 : ((t + x58 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2512 t x01 x02 x17 x24 x45 x58 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u7 (And.intro u5 (And.intro u1 (And.intro u6 (And.intro u4 u2))))))))) h

theorem clause11543 (t x01 x15 x56 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th2514 t x01 x15 x56 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u3 (And.intro u6 (And.intro u4 u1)))))))) h

theorem clause11544 (t x05 x15 x35 : ℝ) : (((t + ((-1) * x05) + x35) ≥ 1) ∨ (¬ ((t + ((-1) * x15) + x35) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x15)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x05) + x35) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x15) + x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2518 t x05 x15 x35
  exact (fun hh => u0 (hh (And.intro u2 u1))) h

theorem clause11545 (t x02 x03 x05 x23 x34 x36 x56 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x36 ≥ 0)) ∨ (¬ ((t + ((-1) * x02) + x05) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
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
  have u3 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x36 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x02) + x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th2521 t x02 x03 x05 x23 x34 x36 x56 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u6 (And.intro u1 (And.intro u5 (And.intro u10 (And.intro u3 (And.intro u7 (And.intro u2 (And.intro u8 (And.intro u9 u4)))))))))))) h

theorem clause11546 (t x57 x67 x78 : ℝ) : (((t + x57 + ((-1) * x67)) ≥ 1) ∨ (¬ (x57 ≥ 0)) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x57 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : (x57 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th2522 t x57 x67 x78
  exact (fun hh => u0 (hh (And.intro u2 (And.intro u1 u3)))) h

theorem clause11548 (t x12 x13 x23 x24 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + x23 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x23 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2528 t x12 x13 x23 x24 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u3 (And.intro u5 (And.intro u0 u2))))))) h

theorem clause11549 (t x02 x03 x23 x24 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((t + x23 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1)))) := by
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
  have u3 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2529 t x02 x03 x23 x24 x36
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u3 (And.intro u4 (And.intro u5 (And.intro u2 u0)))))) h

theorem clause11551 (x02 x03 x04 : ℝ) : ((¬ ((x02 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ ((x02 + ((-1) * x04)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x02 + ((-1) * x04)) ≤ 0) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2531 x02 x03 x04
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause11552 (t x23 x34 x37 : ℝ) : ((¬ (x23 ≥ 0)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ ((t + ((-1) * x34) + x37) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x34) + x37) ≥ 1) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th2532 t x23 x34 x37
  exact (fun hh => u3 (hh (And.intro u2 (And.intro u0 u1)))) h

theorem clause11553 (t x03 x23 x34 x35 x47 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ ((t + ((-1) * x47)) ≤ 0)) := by
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
  have u3 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2540 t x03 x23 x34 x35 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u6 (And.intro u3 (And.intro u5 (And.intro u1 (And.intro u4 u0)))))))) h

theorem clause11554 (t x01 x02 x15 x24 x46 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
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
  have h := NineTheoryTrial.th2542 t x01 x02 x15 x24 x46 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u3 (And.intro u4 (And.intro u1 (And.intro u6 (And.intro u0 (And.intro u2 u5))))))))) h

theorem clause11555 (t x02 x25 x26 x35 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x35) + x45) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x56)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x35) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x25 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2543 t x02 x25 x26 x35 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u6 (And.intro u5 (And.intro u2 (And.intro u3 (And.intro u1 u0)))))))) h

theorem clause11556 (x02 x25 x26 : ℝ) : ((¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x26)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x25 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2544 x02 x25 x26
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 u0))) h

theorem clause11557 (t x01 x03 x15 x36 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x67) + x68) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x67) + x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2550 t x01 x03 x15 x36 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u6 (And.intro u2 (And.intro u4 (And.intro u7 (And.intro u3 (And.intro u1 u5))))))))) h

theorem clause11558 (t x03 x04 x34 x36 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x34) + x36) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x34) + x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2555 t x03 x04 x34 x36 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u4 (And.intro u1 (And.intro u3 u2))))))) h

theorem clause11559 (x02 x03 x04 : ℝ) : ((¬ ((x02 + ((-1) * x03)) ≤ 0)) ∨ ((x03 + ((-1) * x04)) ≥ 0) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x04)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2556 x02 x03 x04
  exact (fun hh => u1 (hh (And.intro u0 u2))) h

theorem clause11560 (t x01 x02 x15 x24 x26 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x46 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
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
  have u3 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x46 + ((-1) * x56)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th2557 t x01 x02 x15 x24 x26 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u5 (And.intro u1 (And.intro u6 (And.intro u3 (And.intro u8 u7)))))))))) h

theorem clause11561 (t x05 x23 x35 x36 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((t + ((-1) * x05) + x35) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x05) + x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2558 t x05 x23 x35 x36 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u2 u5))))))) h

theorem clause11562 (x23 x35 x36 : ℝ) : ((¬ ((x35 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1)))) := by
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
  have u2 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2559 x23 x35 x36
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u2 u1))) h

theorem clause11563 (t x01 x02 x12 x15 x17 x24 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x15) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x17) + x67) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≤ 0) := by
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
  have u5 : ((t + ((-1) * x12) + x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x15)) ≥ 1) := by
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
  have h := NineTheoryTrial.th2561 t x01 x02 x12 x15 x17 x24 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u4 (And.intro u6 (And.intro u7 (And.intro u5 (And.intro u8 (And.intro u3 u2)))))))))) h

theorem clause11564 (t x01 x02 x03 x12 x15 x16 x23 x35 x36 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ (x35 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ ((t + ((-1) * x68)) ≤ 0) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x12) + x15) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x68)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≤ 0) := by
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
  have u4 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x12) + x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x16 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th2562 t x01 x02 x03 x12 x15 x16 x23 x35 x36 x68
  exact (fun hh => (fun hh => hh u11) (hh (And.intro u10 (And.intro u6 (And.intro u7 (And.intro u4 (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u8 (And.intro u0 (And.intro u9 u5)))))))))))) h

theorem clause11565 (t x01 x02 x03 x12 x15 x16 x36 x46 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + ((-1) * x16) + x46) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x12) + x15) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x16) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x12) + x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th2563 t x01 x02 x03 x12 x15 x16 x36 x46 x68
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u6 (And.intro u7 (And.intro u8 (And.intro u4 (And.intro u9 (And.intro u2 (And.intro u1 (And.intro u0 u5)))))))))) h

theorem clause11566 (t x02 x03 x05 x12 x15 x34 x46 x57 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x15) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x15)) ≥ 0)) ∨ (¬ ((t + x68 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x03)) ≥ 0) := by
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
  have u6 : ((t + ((-1) * x12) + x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x05 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((t + x68 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th2564 t x02 x03 x05 x12 x15 x34 x46 x57 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u9 (And.intro u10 (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u8 (And.intro u0 (And.intro u4 (And.intro u5 u7)))))))))))) h

theorem clause11567 (t x02 x03 x07 x23 x34 x37 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((t + x37 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((t + ((-1) * x02) + x07) ≥ 1))) := by
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
  have u3 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x37 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x23 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x02) + x07) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th2565 t x02 x03 x07 x23 x34 x37 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u8 (And.intro u3 (And.intro u0 (And.intro u5 (And.intro u4 (And.intro u6 (And.intro u7 (And.intro u1 u2)))))))))) h

theorem clause11568 (t x02 x03 x36 x46 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ (x68 ≥ 0)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x68 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2570 t x02 x03 x36 x46 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u7 (And.intro u6 (And.intro u3 (And.intro u1 (And.intro u2 u4))))))))) h

theorem clause11569 (t x23 x34 x35 x45 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((t + x45 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x45)) ≥ 0) := by
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
  have u4 : ((t + x45 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2573 t x23 x34 x35 x45 x47
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u0 (And.intro u2 (And.intro u4 (And.intro u3 u1)))))) h

theorem clause11570 (t x04 x23 x34 x35 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((t + x45 + ((-1) * x46)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
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
  have u5 : ((x04 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x45 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2574 t x04 x23 x34 x35 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u4 u6)))))))) h

theorem clause11571 (t x01 x04 x15 x24 x46 x47 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x04)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + x47 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x01 + ((-1) * x04)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x47 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2576 t x01 x04 x15 x24 x46 x47 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u7 (And.intro u3 (And.intro u1 u2))))))))) h

theorem clause11572 (x26 x36 x67 : ℝ) : ((¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x36)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x26 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2580 x26 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 u0)))) h

theorem clause11573 (t x01 x02 x03 x15 x23 x35 x37 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ (x35 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1))) := by
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
  have u3 : (x35 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x03 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th2583 t x01 x02 x03 x15 x23 x35 x37 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u2 (And.intro u0 (And.intro u10 (And.intro u9 (And.intro u1 (And.intro u4 (And.intro u3 (And.intro u8 (And.intro u6 u5)))))))))))) h

theorem clause11574 (t x23 x35 x36 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ (x35 ≥ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2585 t x23 x35 x36 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u3 (And.intro u5 (And.intro u0 (And.intro u6 u2)))))))) h

theorem clause11575 (t x04 x23 x34 x37 x45 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x45) + x47) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x47)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x45) + x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2593 t x04 x23 x34 x37 x45 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u6 (And.intro u3 (And.intro u4 u5)))))))) h

theorem clause11576 (x23 x34 x37 : ℝ) : ((¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x37)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x37)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2594 x23 x34 x37
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u2 u0))) h

theorem clause11577 (t x02 x24 x45 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ (x67 ≥ 0))) := by
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
  have u3 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2595 t x02 x24 x45 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u6 (And.intro u1 (And.intro u5 (And.intro u3 (And.intro u2 u4)))))))) h

theorem clause11578 (t x02 x03 x23 x34 x37 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x56 ≥ 0)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x37 + ((-1) * x67)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1))) := by
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
  have u3 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x37 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x23 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th2596 t x02 x03 x23 x34 x37 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u8 (And.intro u3 (And.intro u6 (And.intro u2 (And.intro u1 (And.intro u5 (And.intro u7 u4)))))))))) h

theorem clause11579 (t x01 x04 x05 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((t + x01 + ((-1) * x05)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x01 + ((-1) * x05)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2598 t x01 x04 x05 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u4 u2))))))) h

theorem clause11580 (x03 x34 x35 : ℝ) : (((x03 + ((-1) * x35)) ≥ 1) ∨ (¬ ((x34 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2600 x03 x34 x35
  exact (fun hh => u0 (hh (And.intro u2 u1))) h

theorem clause11581 (t x03 x23 x25 x35 x56 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((t + ((-1) * x03) + x23) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x03) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2601 t x03 x23 x25 x35 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u1 u2))))))) h

theorem clause11582 (t x03 x23 x26 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x03) + x23) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x26)) ≤ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x03) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2602 t x03 x23 x26 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u4 u5))))))) h

theorem clause11583 (x25 x56 x57 : ℝ) : ((¬ ((x56 + ((-1) * x57)) ≥ 0)) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ ((x25 + ((-1) * x57)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x56 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x25 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2604 x25 x56 x57
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause11584 (x24 x25 x46 x56 : ℝ) : ((¬ ((x46 + ((-1) * x56)) ≤ 0)) ∨ ((x24 + ((-1) * x46)) ≥ 1) ∨ (¬ ((x24 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x46 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th2608 x24 x25 x46 x56
  exact (fun hh => u1 (hh (And.intro u0 (And.intro u3 u2)))) h

theorem clause11585 (t x01 x02 x17 x24 x46 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((t + x68 + ((-1) * x78)) ≥ 1))) := by
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
  have u3 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x68 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2609 t x01 x02 x17 x24 x46 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u7 (And.intro u4 (And.intro u6 (And.intro u1 (And.intro u0 u3))))))))) h

theorem clause11586 (t x15 x17 x45 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x15) + x45) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x17)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x15) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x17)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2610 t x15 x17 x45 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u3 (And.intro u1 (And.intro u0 u2))))))) h

theorem clause11587 (t x05 x25 x45 x56 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ (x45 ≥ 0)) ∨ ((t + ((-1) * x78)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x25 + ((-1) * x56)) ≥ 1) := by
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
  have u6 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2613 t x05 x25 x45 x56 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u3 (And.intro u0 (And.intro u5 (And.intro u6 (And.intro u4 u7))))))))) h

theorem clause11588 (t x03 x25 x35 x36 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x25 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x25 + ((-1) * x35)) ≥ 1) := by
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
  have u4 : ((x36 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2621 t x03 x25 x35 x36 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u3 (And.intro u4 (And.intro u2 u1))))))) h

theorem clause11589 (x25 x56 x57 : ℝ) : ((¬ ((x56 + ((-1) * x57)) ≥ 0)) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x56 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2623 x25 x56 x57
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u1 u2))) h

theorem clause11590 (t x01 x14 x45 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ ((t + ((-1) * x78)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2624 t x01 x14 x45 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u4 (And.intro u6 u3)))))))) h

theorem clause11593 (t x23 x34 x46 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2631 t x23 x34 x46 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u5 (And.intro u4 (And.intro u6 (And.intro u3 u1)))))))) h

theorem clause11594 (t x01 x16 x46 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x16 + ((-1) * x68)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2632 t x01 x16 x46 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u6 (And.intro u4 (And.intro u5 (And.intro u3 (And.intro u1 u2)))))))) h

theorem clause11595 (t x13 x17 x23 x37 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x13) + x23) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x17)) ≥ 0)) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x13) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x13 + ((-1) * x17)) ≥ 0) := by
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
  have h := NineTheoryTrial.th2635 t x13 x17 x23 x37 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u3 (And.intro u4 u5))))))) h

theorem clause11596 (x25 x35 x57 : ℝ) : (((x35 + ((-1) * x57)) ≥ 1) ∨ (¬ ((x25 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x25 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2637 x25 x35 x57
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause11598 (t x04 x06 x45 x46 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x45) + x46) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x06)) ≥ 0)) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x45) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2641 t x04 x06 x45 x46 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u4 (And.intro u3 u1))))))) h

theorem clause11599 (t x03 x35 x36 x46 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ (x46 ≥ 0)) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ ((t + ((-1) * x35)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2642 t x03 x35 x36 x46 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u6 (And.intro u2 (And.intro u3 (And.intro u4 u1)))))))) h

theorem clause11600 (t x01 x02 x03 x16 x34 x46 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + x67 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x68)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x03)) ≥ 0) := by
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
  have u6 : ((t + x67 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x16 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th2643 t x01 x02 x03 x16 x34 x46 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u8 (And.intro u3 (And.intro u0 (And.intro u6 (And.intro u4 (And.intro u1 (And.intro u5 u2)))))))))) h

theorem clause11601 (t x01 x05 x16 x25 x56 x58 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x05 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x05)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x01 + ((-1) * x05)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x25 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th2644 t x01 x05 x16 x25 x56 x58 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u8 (And.intro u2 (And.intro u9 (And.intro u0 (And.intro u3 (And.intro u7 (And.intro u1 (And.intro u4 u6))))))))))) h

theorem clause11602 (t x14 x16 x45 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x45) + x46) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x16)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x45) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2645 t x14 x16 x45 x46 x67
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u3 (And.intro u4 (And.intro u2 (And.intro u1 u0)))))) h

theorem clause11603 (t x01 x02 x16 x25 x58 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((t + x58 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x25)) ≥ 1) := by
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
  have u5 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2647 t x01 x02 x16 x25 x58 x67 x78
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u6 (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u3 u7)))))))) h

theorem clause11604 (x46 x56 x67 : ℝ) : ((¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x46 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2648 x46 x56 x67
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 u0))) h

theorem clause11605 (t x25 x26 x35 x46 x56 x58 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x25 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((t + x56 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x25 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x56 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x35 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2650 t x25 x26 x35 x46 x56 x58 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u4 (And.intro u6 (And.intro u0 (And.intro u5 (And.intro u3 u7))))))))) h

theorem clause11606 (t x01 x02 x16 x24 x45 x58 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((t + x58 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x68)) ≤ (-1)))) := by
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
  have u4 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x58 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x16 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2651 t x01 x02 x16 x24 x45 x58 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u5 (And.intro u4 (And.intro u6 (And.intro u0 (And.intro u1 (And.intro u2 u3))))))))) h

theorem clause11607 (t x03 x23 x24 x34 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((t + ((-1) * x03) + x23) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x03) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2654 t x03 x23 x24 x34 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u0 (And.intro u2 (And.intro u1 u5))))))) h

theorem clause11608 (x34 x46 x47 : ℝ) : ((¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x47)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x46 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2656 x34 x46 x47
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u2 u0))) h

theorem clause11609 (t x34 x46 x47 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x67) + x68) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x47 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x67) + x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2657 t x34 x46 x47 x67 x68
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u3 (And.intro u2 (And.intro u4 (And.intro u0 u1)))))) h

theorem clause11610 (t x14 x17 x45 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x14 + ((-1) * x17)) ≥ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x45) + x47) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x17)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x45) + x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2659 t x14 x17 x45 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u5 u2))))))) h

theorem clause11612 (t x02 x16 x24 x45 x56 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((t + ((-1) * x16) + x56) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ (x57 ≥ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
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
  have u3 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x16) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x57 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th2662 t x02 x16 x24 x45 x56 x57 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u7 (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u3 (And.intro u6 (And.intro u9 (And.intro u5 u8))))))))))) h

theorem clause11613 (t x02 x24 x45 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
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
  have u3 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2663 t x02 x24 x45 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u3 (And.intro u4 (And.intro u5 (And.intro u2 (And.intro u1 u0)))))))) h

theorem clause11614 (t x02 x25 x56 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2664 t x02 x25 x56 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u6 (And.intro u3 (And.intro u5 (And.intro u2 (And.intro u4 u1)))))))) h

theorem clause11615 (t x23 x36 x46 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x68)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2667 t x23 x36 x46 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u6 (And.intro u4 (And.intro u2 (And.intro u3 (And.intro u1 u5)))))))) h

theorem clause11616 (t x02 x03 x36 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1))) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ (x67 ≥ 0)) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2671 t x02 x03 x36 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u5 (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u4 (And.intro u3 u6))))))))) h

theorem clause11617 (t x01 x02 x17 x25 x56 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((t + x68 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x25)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x68 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2672 t x01 x02 x17 x25 x56 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u7 (And.intro u4 (And.intro u1 (And.intro u3 (And.intro u0 (And.intro u6 u5))))))))) h

theorem clause11618 (t x03 x13 x23 x34 x36 x46 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x13) + x23) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((t + x67 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x13) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
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
  have u8 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th2675 t x03 x13 x23 x34 x36 x46 x67 x68
  exact (fun hh => (fun hh => hh u8) (hh (And.intro u2 (And.intro u4 (And.intro u1 (And.intro u5 (And.intro u7 (And.intro u6 (And.intro u3 u0))))))))) h

theorem clause11619 (t x05 x13 x15 x23 x35 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x13) + x23) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x15)) ≥ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x13) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x05 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2679 t x05 x13 x15 x23 x35 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u4 u6)))))))) h

theorem clause11620 (t x04 x24 x45 x47 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x45 ≥ 0)) ∨ ((t + ((-1) * x57)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2680 t x04 x24 x45 x47 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u1 (And.intro u6 (And.intro u7 (And.intro u0 (And.intro u3 u4))))))))) h

theorem clause11623 (t x03 x23 x25 x35 x57 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((t + ((-1) * x03) + x23) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1)))) := by
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
  have u3 : ((x23 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x03) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2685 t x03 x23 x25 x35 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u1 u5))))))) h

theorem clause11624 (t x01 x02 x14 x25 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x56) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2686 t x01 x02 x14 x25 x45 x56 x57
  exact (fun hh => (fun hh => hh u7) (hh (And.intro u6 (And.intro u5 (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u4 u2)))))))) h

theorem clause11626 (t x23 x36 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ ((t + ((-1) * x57)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2688 t x23 x36 x57 x67 x78
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u3 (And.intro u2 (And.intro u4 (And.intro u5 (And.intro u1 u0))))))) h

theorem clause11628 (t x04 x05 x23 x34 x45 x56 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x45 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x45 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x05 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th2692 t x04 x05 x23 x34 x45 x56 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u6 (And.intro u3 (And.intro u1 (And.intro u5 (And.intro u8 (And.intro u7 u4)))))))))) h

theorem clause11629 (t x24 x26 x45 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x45 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x26)) ≤ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1)))) := by
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
  have h := NineTheoryTrial.th2693 t x24 x26 x45 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u5 (And.intro u3 (And.intro u0 u1))))))) h

theorem clause11630 (t x24 x45 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x45 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x45)) ≥ 1) := by
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
  have u4 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2694 t x24 x45 x46 x56 x67
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u1 (And.intro u6 (And.intro u4 (And.intro u2 (And.intro u5 u0))))))) h

theorem clause11631 (t x01 x02 x14 x25 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x25 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2696 t x01 x02 x14 x25 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u5 (And.intro u4 u3))))))) h

theorem clause11633 (x27 x57 x78 : ℝ) : ((¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x27 + ((-1) * x57)) ≤ 0)) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x27 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2698 x27 x57 x78
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u0 u2))) h

theorem clause11634 (x57 x67 x78 : ℝ) : ((¬ ((x57 + ((-1) * x67)) ≥ 0)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ ((x67 + ((-1) * x78)) ≤ (-1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x57 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x67 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2699 x57 x67 x78
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause11635 (x57 x67 x78 : ℝ) : ((¬ ((x57 + ((-1) * x67)) ≥ 0)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x57 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2700 x57 x67 x78
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 u0))) h

theorem clause11636 (t x01 x02 x15 x26 x57 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ ((t + x68 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x68)) ≥ 1) := by
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
  have h := NineTheoryTrial.th2701 t x01 x02 x15 x26 x57 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u4 (And.intro u6 (And.intro u0 (And.intro u7 (And.intro u5 u1))))))))) h

theorem clause11638 (t x01 x02 x15 x26 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x46 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x46 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x26)) ≥ 1) := by
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
  have h := NineTheoryTrial.th2705 t x01 x02 x15 x26 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u0 (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u2 (And.intro u3 u7))))))))) h

theorem clause11639 (t x24 x26 x45 x46 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x45 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x26)) ≤ 0)) ∨ (¬ ((x26 + ((-1) * x68)) ≤ (-1)))) := by
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
  have u3 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2708 t x24 x26 x45 x46 x68
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u4 u3)))))) h

theorem clause11640 (x06 x36 x56 : ℝ) : ((¬ ((x06 + ((-1) * x36)) ≥ 0)) ∨ ((x36 + ((-1) * x56)) ≤ 0) ∨ (¬ ((x06 + ((-1) * x56)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x06 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x36 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2710 x06 x36 x56
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause11641 (t x05 x56 x57 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ (x67 ≥ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
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
  have u5 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2712 t x05 x56 x57 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u2 (And.intro u0 u3)))))))) h

theorem clause11642 (t x04 x05 x45 x46 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((t + x45 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x58)) ≤ (-1)))) := by
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
  have u4 : ((x05 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2713 t x04 x05 x45 x46 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u3 (And.intro u5 (And.intro u1 u4))))))) h

theorem clause11643 (t x01 x02 x15 x24 x45 x56 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + ((-1) * x56) + x58) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
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
  have u4 : ((t + ((-1) * x56) + x58) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x58)) ≥ 1) := by
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
  have h := NineTheoryTrial.th2717 t x01 x02 x15 x24 x45 x56 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u5 (And.intro u7 (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u3 u2))))))))) h

theorem clause11645 (x04 x45 x46 : ℝ) : ((¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ ((x04 + ((-1) * x45)) ≤ (-1)) ∨ (¬ ((x45 + ((-1) * x46)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th2726 x04 x45 x46
  exact (fun hh => u1 (hh (And.intro u0 u2))) h

theorem clause11647 (t x05 x13 x15 x23 x35 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x13) + x23) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x15)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x13) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x05 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2730 t x05 x13 x15 x23 x35 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u5 (And.intro u0 (And.intro u6 (And.intro u3 u2)))))))) h

theorem clause11648 (t x01 x05 x14 x15 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((t + x14 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x05)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x14 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2731 t x01 x05 x14 x15 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u3 (And.intro u4 (And.intro u1 u2))))))) h

theorem clause11649 (t x03 x05 x23 x34 x35 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + x34 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1)))) := by
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
  have u3 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x23)) ≥ 0) := by
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
  have h := NineTheoryTrial.th2734 t x03 x05 x23 x34 x35 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u4 (And.intro u3 (And.intro u6 (And.intro u0 (And.intro u1 u5)))))))) h

theorem clause11650 (t x01 x02 x04 x14 x23 x35 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((t + x35 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x35 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th2737 t x01 x02 x04 x14 x23 x35 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u4 (And.intro u8 (And.intro u1 (And.intro u6 (And.intro u7 (And.intro u0 u5)))))))))) h

theorem clause11652 (x04 x05 x47 x57 : ℝ) : ((¬ ((x04 + ((-1) * x05)) ≤ 0)) ∨ ((x04 + ((-1) * x47)) ≤ (-1)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x57)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x47 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th2744 x04 x05 x47 x57
  exact (fun hh => u1 (hh (And.intro u2 (And.intro u3 u0)))) h

theorem clause11653 (t x03 x34 x35 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ (x34 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x34)) ≥ 1) := by
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
  have u4 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2745 t x03 x34 x35 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u6 (And.intro u4 (And.intro u2 (And.intro u0 u5)))))))) h

theorem clause11654 (t x05 x23 x34 x35 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x35)) ≥ 0)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ (x34 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2746 t x05 x23 x34 x35 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u2 (And.intro u5 (And.intro u7 u1))))))))) h

theorem clause11655 (t x06 x23 x35 x36 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x35 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x35 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2748 t x06 x23 x35 x36 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u6 (And.intro u3 u4)))))))) h

theorem clause11656 (t x01 x02 x04 x14 x23 x35 x45 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((t + x35 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x35 + ((-1) * x45)) ≥ 1) := by
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
  have u5 : ((x14 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th2749 t x01 x02 x04 x14 x23 x35 x45 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u6 (And.intro u8 (And.intro u5 u7)))))))))) h

theorem clause11658 (t x01 x02 x14 x23 x36 x47 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((t + ((-1) * x47) + x67) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
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
  have u3 : ((t + ((-1) * x47) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th2751 t x01 x02 x14 x23 x36 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u1 (And.intro u6 (And.intro u0 (And.intro u4 (And.intro u3 u7))))))))) h

theorem clause11660 (t x02 x12 x23 x26 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ (x67 ≥ 0))) := by
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
  have u4 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2755 t x02 x12 x23 x26 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u6 (And.intro u2 (And.intro u3 (And.intro u5 u1)))))))) h

theorem clause11661 (t x01 x02 x12 x14 x23 x27 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((t + x27 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1))) := by
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
  have u4 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
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
  have u7 : ((t + x27 + ((-1) * x67)) ≥ 1) := by
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
  have h := NineTheoryTrial.th2758 t x01 x02 x12 x14 x23 x27 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u8 (And.intro u6 (And.intro u4 (And.intro u9 (And.intro u1 (And.intro u7 (And.intro u2 u3))))))))))) h

theorem clause11662 (t x01 x15 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ ((t + ((-1) * x57)) ≤ 0) ∨ (¬ (x01 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th2760 t x01 x15 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u6 (And.intro u5 (And.intro u4 (And.intro u2 (And.intro u1 u3)))))))) h

theorem clause11663 (t x01 x14 x47 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ ((t + ((-1) * x57)) ≤ 0) ∨ (¬ (x01 ≥ 0))) := by
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
  have u3 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2761 t x01 x14 x47 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u6 (And.intro u2 (And.intro u4 (And.intro u5 u3)))))))) h

theorem clause11664 (t x04 x05 x45 x47 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x45) + x47) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x45) + x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th2762 t x04 x05 x45 x47 x56
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u5 (And.intro u0 (And.intro u2 (And.intro u4 u3)))))) h

theorem clause11665 (t x04 x05 x34 x45 x47 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x45) + x47) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x34)) ≥ 0) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x45) + x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th2763 t x04 x05 x34 x45 x47 x56
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u3 (And.intro u4 (And.intro u5 (And.intro u0 (And.intro u2 u6))))))) h

#print axioms clause11665
end NineCNFDirectTrial
