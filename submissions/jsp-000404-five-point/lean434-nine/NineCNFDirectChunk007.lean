import NineTheoryTrial

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineCNFDirectTrial

theorem clause9555 (t x01 x03 x12 x13 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
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
  have u4 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th929 t x01 x03 x12 x13 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u4 u5))))))) h

theorem clause9557 (t x01 x13 x16 x36 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x36)) ≤ 0))) := by
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
  have u3 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x16 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th935 t x01 x13 x16 x36 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u7 (And.intro u6 (And.intro u2 (And.intro u3 (And.intro u1 u4))))))))) h

theorem clause9558 (t x01 x13 x16 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ ((t + ((-1) * x36)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1)))) := by
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
  have u3 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th936 t x01 x13 x16 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u5 (And.intro u0 (And.intro u4 u6)))))))) h

theorem clause9559 (t x01 x06 x12 x13 x16 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x16)) ≥ 0))) := by
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
  have u3 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th937 t x01 x06 x12 x13 x16 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u6 (And.intro u0 (And.intro u2 (And.intro u5 (And.intro u4 u3)))))))) h

theorem clause9560 (x02 x12 x26 : ℝ) : (((x02 + ((-1) * x12)) ≥ 0) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x12)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th938 x02 x12 x26
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 u1)))) h

theorem clause9562 (t x16 : ℝ) : ((¬ ((t + ((-1) * x16)) ≤ 0)) ∨ (t ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x16) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th940 t x16
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause9564 (t x16 : ℝ) : ((¬ (t ≤ x16)) ∨ (¬ (x16 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x16 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th941 t x16
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause9566 (t x16 : ℝ) (h : (x16 < t)) : ((x16 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 < t) := fun hh => hn hh
  exact u0 h

theorem clause9567 (t x02 x06 x23 x26 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + x23 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x06)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x23)) ≥ 1) := by
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
  have u4 : ((t + x23 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th943 t x02 x06 x23 x26 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u5 u3))))))) h

theorem clause9569 (t x01 x12 x13 x23 x25 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((t + x23 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1)))) := by
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
  have u4 : ((t + x23 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th947 t x01 x12 x13 x23 x25
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u5 u3))))))) h

theorem clause9570 (t x02 x04 x24 x26 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((t + x24 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x24 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th948 t x02 x04 x24 x26 x45
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u3 u4)))))) h

theorem clause9571 (t x13 x24 x34 x37 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((t + x24 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x47)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x24 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th949 t x13 x24 x34 x37 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u4 (And.intro u5 u1))))))) h

theorem clause9572 (t x01 x14 x17 x24 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x47)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x14) + x24) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x17 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x14) + x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th950 t x01 x14 x17 x24 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u2 (And.intro u3 (And.intro u0 u5))))))) h

theorem clause9573 (t x04 x05 x24 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x04) + x24) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x04) + x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th955 t x04 x05 x24 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u5 u4))))))) h

theorem clause9574 (t x04 x05 x14 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x04) + x14) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1)))) := by
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
  have u4 : ((t + ((-1) * x04) + x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th956 t x04 x05 x14 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u4 (And.intro u0 (And.intro u2 u1))))))) h

theorem clause9575 (t x01 x05 x12 x13 x15 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x15)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x05)) ≤ 0))) := by
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
  have u3 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th957 t x01 x05 x12 x13 x15 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u1 (And.intro u6 (And.intro u0 (And.intro u3 u4)))))))) h

theorem clause9576 (t x01 x05 x12 x13 x15 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x15)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x05)) ≤ 0))) := by
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
  have u3 : ((x12 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th960 t x01 x05 x12 x13 x15 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u4 (And.intro u3 (And.intro u0 (And.intro u5 u6)))))))) h

theorem clause9578 (t x01 x12 x15 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
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
  have h := NineTheoryTrial.th963 t x01 x12 x15 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u4 u3)))))))) h

theorem clause9579 (t x02 x07 x24 x45 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x07)) ≥ 0))) := by
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
  have u3 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x07)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th965 t x02 x07 x24 x45 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u4 (And.intro u2 (And.intro u7 (And.intro u1 (And.intro u0 u6))))))))) h

theorem clause9581 (t x04 x24 x45 x46 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ ((t + ((-1) * x46)) ≤ 0) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ (x45 ≥ 0))) := by
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
  have u3 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th968 t x04 x24 x45 x46 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u0 (And.intro u6 (And.intro u2 u3)))))))) h

theorem clause9582 (x02 x04 x06 : ℝ) : ((¬ ((x02 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x06)) ≥ 0)) ∨ ((x02 + ((-1) * x06)) ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x02 + ((-1) * x06)) ≥ 0) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th969 x02 x04 x06
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause9583 (t x02 x03 x26 x35 x58 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x58) + x78) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
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
  have u3 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x26)) ≥ 1) := by
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
  have u7 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th976 t x02 x03 x26 x35 x58 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u1 (And.intro u7 (And.intro u6 (And.intro u4 (And.intro u3 u5))))))))) h

theorem clause9591 (t x15 x18 x58 : ℝ) : (((x15 + ((-1) * x58)) ≥ 1) ∨ ((x18 + ((-1) * x58)) ≤ 0) ∨ (¬ (x15 ≤ x18)) ∨ (¬ (x18 ≤ x58)) ∨ (¬ ((x58 - x15) ≥ 1)) ∨ (¬ ((x18 - x15) ≤ (t - 1))) ∨ (¬ ((x58 - x18) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x58)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 + ((-1) * x58)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x18) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x18 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x58 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x18 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x18) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th979 t x15 x18 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9594 (t x15 x18 x58 : ℝ) : (((x15 + ((-1) * x58)) ≤ (-1)) ∨ ((x18 + ((-1) * x58)) ≥ 0) ∨ (¬ (x15 ≤ x18)) ∨ (¬ (x18 ≤ x58)) ∨ (¬ ((x58 - x15) ≥ 1)) ∨ (¬ ((x18 - x15) ≤ (t - 1))) ∨ (¬ ((x58 - x18) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x58)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 + ((-1) * x58)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x18) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x18 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x58 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x18 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x18) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th979 t x15 x18 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9596 (t x15 x18 x58 : ℝ) : (((x15 + ((-1) * x58)) ≤ (-1)) ∨ ((x15 + ((-1) * x58)) ≥ 1) ∨ (¬ (x15 ≤ x18)) ∨ (¬ (x18 ≤ x58)) ∨ (¬ ((x58 - x15) ≥ 1)) ∨ (¬ ((x18 - x15) ≤ (t - 1))) ∨ (¬ ((x58 - x18) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x58)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x58)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x18) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x18 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x58 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x18 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x18) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th979 t x15 x18 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9616 (t x15 x18 x58 : ℝ) : (((x15 + ((-1) * x58)) ≥ 1) ∨ ((x18 + ((-1) * x58)) ≤ 0) ∨ (¬ (x58 ≤ x18)) ∨ (¬ (x18 ≤ x15)) ∨ (¬ ((x15 - x58) ≥ 1)) ∨ (¬ ((x15 - x18) ≤ (t - 1))) ∨ (¬ ((x18 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x58)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 + ((-1) * x58)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x58 ≤ x18) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x18 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x58) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x18) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x18 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th979 t x15 x18 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9619 (t x15 x18 x58 : ℝ) : (((x15 + ((-1) * x58)) ≤ (-1)) ∨ ((x18 + ((-1) * x58)) ≥ 0) ∨ (¬ (x58 ≤ x18)) ∨ (¬ (x18 ≤ x15)) ∨ (¬ ((x15 - x58) ≥ 1)) ∨ (¬ ((x15 - x18) ≤ (t - 1))) ∨ (¬ ((x18 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x58)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 + ((-1) * x58)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x58 ≤ x18) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x18 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x58) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x18) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x18 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th979 t x15 x18 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9621 (t x15 x18 x58 : ℝ) : (((x15 + ((-1) * x58)) ≤ (-1)) ∨ ((x15 + ((-1) * x58)) ≥ 1) ∨ (¬ (x58 ≤ x18)) ∨ (¬ (x18 ≤ x15)) ∨ (¬ ((x15 - x58) ≥ 1)) ∨ (¬ ((x15 - x18) ≤ (t - 1))) ∨ (¬ ((x18 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x58)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x58)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x58 ≤ x18) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x18 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x58) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x18) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x18 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th979 t x15 x18 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9684 (t x15 x18 x58 : ℝ) (h : (((x15 ≤ x18) ∧ (x18 ≤ x58) ∧ ((x58 - x15) ≥ 1) ∧ ((x18 - x15) ≤ (t - 1)) ∧ ((x58 - x18) ≤ (t - 1))) ∨ ((x58 ≤ x18) ∧ (x18 ≤ x15) ∧ ((x15 - x58) ≥ 1) ∧ ((x15 - x18) ≤ (t - 1)) ∧ ((x18 - x58) ≤ (t - 1))))) : ((x15 ≤ x18) ∨ (x58 ≤ x18)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x18) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9685 (t x15 x18 x58 : ℝ) (h : (((x15 ≤ x18) ∧ (x18 ≤ x58) ∧ ((x58 - x15) ≥ 1) ∧ ((x18 - x15) ≤ (t - 1)) ∧ ((x58 - x18) ≤ (t - 1))) ∨ ((x58 ≤ x18) ∧ (x18 ≤ x15) ∧ ((x15 - x58) ≥ 1) ∧ ((x15 - x18) ≤ (t - 1)) ∧ ((x18 - x58) ≤ (t - 1))))) : ((x15 ≤ x18) ∨ (x18 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9686 (t x15 x18 x58 : ℝ) (h : (((x15 ≤ x18) ∧ (x18 ≤ x58) ∧ ((x58 - x15) ≥ 1) ∧ ((x18 - x15) ≤ (t - 1)) ∧ ((x58 - x18) ≤ (t - 1))) ∨ ((x58 ≤ x18) ∧ (x18 ≤ x15) ∧ ((x15 - x58) ≥ 1) ∧ ((x15 - x18) ≤ (t - 1)) ∧ ((x18 - x58) ≤ (t - 1))))) : ((x15 ≤ x18) ∨ ((x15 - x58) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x58) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9687 (t x15 x18 x58 : ℝ) (h : (((x15 ≤ x18) ∧ (x18 ≤ x58) ∧ ((x58 - x15) ≥ 1) ∧ ((x18 - x15) ≤ (t - 1)) ∧ ((x58 - x18) ≤ (t - 1))) ∨ ((x58 ≤ x18) ∧ (x18 ≤ x15) ∧ ((x15 - x58) ≥ 1) ∧ ((x15 - x18) ≤ (t - 1)) ∧ ((x18 - x58) ≤ (t - 1))))) : ((x15 ≤ x18) ∨ ((x15 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9688 (t x15 x18 x58 : ℝ) (h : (((x15 ≤ x18) ∧ (x18 ≤ x58) ∧ ((x58 - x15) ≥ 1) ∧ ((x18 - x15) ≤ (t - 1)) ∧ ((x58 - x18) ≤ (t - 1))) ∨ ((x58 ≤ x18) ∧ (x18 ≤ x15) ∧ ((x15 - x58) ≥ 1) ∧ ((x15 - x18) ≤ (t - 1)) ∧ ((x18 - x58) ≤ (t - 1))))) : ((x15 ≤ x18) ∨ ((x18 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9689 (t x15 x18 x58 : ℝ) (h : (((x15 ≤ x18) ∧ (x18 ≤ x58) ∧ ((x58 - x15) ≥ 1) ∧ ((x18 - x15) ≤ (t - 1)) ∧ ((x58 - x18) ≤ (t - 1))) ∨ ((x58 ≤ x18) ∧ (x18 ≤ x15) ∧ ((x15 - x58) ≥ 1) ∧ ((x15 - x18) ≤ (t - 1)) ∧ ((x18 - x58) ≤ (t - 1))))) : ((x18 ≤ x58) ∨ (x58 ≤ x18)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x18 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x18) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9690 (t x15 x18 x58 : ℝ) (h : (((x15 ≤ x18) ∧ (x18 ≤ x58) ∧ ((x58 - x15) ≥ 1) ∧ ((x18 - x15) ≤ (t - 1)) ∧ ((x58 - x18) ≤ (t - 1))) ∨ ((x58 ≤ x18) ∧ (x18 ≤ x15) ∧ ((x15 - x58) ≥ 1) ∧ ((x15 - x18) ≤ (t - 1)) ∧ ((x18 - x58) ≤ (t - 1))))) : ((x18 ≤ x58) ∨ (x18 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x18 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9691 (t x15 x18 x58 : ℝ) (h : (((x15 ≤ x18) ∧ (x18 ≤ x58) ∧ ((x58 - x15) ≥ 1) ∧ ((x18 - x15) ≤ (t - 1)) ∧ ((x58 - x18) ≤ (t - 1))) ∨ ((x58 ≤ x18) ∧ (x18 ≤ x15) ∧ ((x15 - x58) ≥ 1) ∧ ((x15 - x18) ≤ (t - 1)) ∧ ((x18 - x58) ≤ (t - 1))))) : ((x18 ≤ x58) ∨ ((x15 - x58) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x18 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x58) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9692 (t x15 x18 x58 : ℝ) (h : (((x15 ≤ x18) ∧ (x18 ≤ x58) ∧ ((x58 - x15) ≥ 1) ∧ ((x18 - x15) ≤ (t - 1)) ∧ ((x58 - x18) ≤ (t - 1))) ∨ ((x58 ≤ x18) ∧ (x18 ≤ x15) ∧ ((x15 - x58) ≥ 1) ∧ ((x15 - x18) ≤ (t - 1)) ∧ ((x18 - x58) ≤ (t - 1))))) : ((x18 ≤ x58) ∨ ((x15 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x18 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9693 (t x15 x18 x58 : ℝ) (h : (((x15 ≤ x18) ∧ (x18 ≤ x58) ∧ ((x58 - x15) ≥ 1) ∧ ((x18 - x15) ≤ (t - 1)) ∧ ((x58 - x18) ≤ (t - 1))) ∨ ((x58 ≤ x18) ∧ (x18 ≤ x15) ∧ ((x15 - x58) ≥ 1) ∧ ((x15 - x18) ≤ (t - 1)) ∧ ((x18 - x58) ≤ (t - 1))))) : ((x18 ≤ x58) ∨ ((x18 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x18 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9694 (t x15 x18 x58 : ℝ) (h : (((x15 ≤ x18) ∧ (x18 ≤ x58) ∧ ((x58 - x15) ≥ 1) ∧ ((x18 - x15) ≤ (t - 1)) ∧ ((x58 - x18) ≤ (t - 1))) ∨ ((x58 ≤ x18) ∧ (x18 ≤ x15) ∧ ((x15 - x58) ≥ 1) ∧ ((x15 - x18) ≤ (t - 1)) ∧ ((x18 - x58) ≤ (t - 1))))) : (((x58 - x15) ≥ 1) ∨ (x58 ≤ x18)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x15) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x18) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9695 (t x15 x18 x58 : ℝ) (h : (((x15 ≤ x18) ∧ (x18 ≤ x58) ∧ ((x58 - x15) ≥ 1) ∧ ((x18 - x15) ≤ (t - 1)) ∧ ((x58 - x18) ≤ (t - 1))) ∨ ((x58 ≤ x18) ∧ (x18 ≤ x15) ∧ ((x15 - x58) ≥ 1) ∧ ((x15 - x18) ≤ (t - 1)) ∧ ((x18 - x58) ≤ (t - 1))))) : (((x58 - x15) ≥ 1) ∨ (x18 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x15) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9696 (t x15 x18 x58 : ℝ) (h : (((x15 ≤ x18) ∧ (x18 ≤ x58) ∧ ((x58 - x15) ≥ 1) ∧ ((x18 - x15) ≤ (t - 1)) ∧ ((x58 - x18) ≤ (t - 1))) ∨ ((x58 ≤ x18) ∧ (x18 ≤ x15) ∧ ((x15 - x58) ≥ 1) ∧ ((x15 - x18) ≤ (t - 1)) ∧ ((x18 - x58) ≤ (t - 1))))) : (((x58 - x15) ≥ 1) ∨ ((x15 - x58) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x15) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x58) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9697 (t x15 x18 x58 : ℝ) (h : (((x15 ≤ x18) ∧ (x18 ≤ x58) ∧ ((x58 - x15) ≥ 1) ∧ ((x18 - x15) ≤ (t - 1)) ∧ ((x58 - x18) ≤ (t - 1))) ∨ ((x58 ≤ x18) ∧ (x18 ≤ x15) ∧ ((x15 - x58) ≥ 1) ∧ ((x15 - x18) ≤ (t - 1)) ∧ ((x18 - x58) ≤ (t - 1))))) : (((x58 - x15) ≥ 1) ∨ ((x15 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x15) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9698 (t x15 x18 x58 : ℝ) (h : (((x15 ≤ x18) ∧ (x18 ≤ x58) ∧ ((x58 - x15) ≥ 1) ∧ ((x18 - x15) ≤ (t - 1)) ∧ ((x58 - x18) ≤ (t - 1))) ∨ ((x58 ≤ x18) ∧ (x18 ≤ x15) ∧ ((x15 - x58) ≥ 1) ∧ ((x15 - x18) ≤ (t - 1)) ∧ ((x18 - x58) ≤ (t - 1))))) : (((x58 - x15) ≥ 1) ∨ ((x18 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x15) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9699 (t x15 x18 x58 : ℝ) (h : (((x15 ≤ x18) ∧ (x18 ≤ x58) ∧ ((x58 - x15) ≥ 1) ∧ ((x18 - x15) ≤ (t - 1)) ∧ ((x58 - x18) ≤ (t - 1))) ∨ ((x58 ≤ x18) ∧ (x18 ≤ x15) ∧ ((x15 - x58) ≥ 1) ∧ ((x15 - x18) ≤ (t - 1)) ∧ ((x18 - x58) ≤ (t - 1))))) : (((x18 - x15) ≤ (t - 1)) ∨ (x58 ≤ x18)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x18) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9700 (t x15 x18 x58 : ℝ) (h : (((x15 ≤ x18) ∧ (x18 ≤ x58) ∧ ((x58 - x15) ≥ 1) ∧ ((x18 - x15) ≤ (t - 1)) ∧ ((x58 - x18) ≤ (t - 1))) ∨ ((x58 ≤ x18) ∧ (x18 ≤ x15) ∧ ((x15 - x58) ≥ 1) ∧ ((x15 - x18) ≤ (t - 1)) ∧ ((x18 - x58) ≤ (t - 1))))) : (((x18 - x15) ≤ (t - 1)) ∨ (x18 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9701 (t x15 x18 x58 : ℝ) (h : (((x15 ≤ x18) ∧ (x18 ≤ x58) ∧ ((x58 - x15) ≥ 1) ∧ ((x18 - x15) ≤ (t - 1)) ∧ ((x58 - x18) ≤ (t - 1))) ∨ ((x58 ≤ x18) ∧ (x18 ≤ x15) ∧ ((x15 - x58) ≥ 1) ∧ ((x15 - x18) ≤ (t - 1)) ∧ ((x18 - x58) ≤ (t - 1))))) : (((x18 - x15) ≤ (t - 1)) ∨ ((x15 - x58) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x58) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9702 (t x15 x18 x58 : ℝ) (h : (((x15 ≤ x18) ∧ (x18 ≤ x58) ∧ ((x58 - x15) ≥ 1) ∧ ((x18 - x15) ≤ (t - 1)) ∧ ((x58 - x18) ≤ (t - 1))) ∨ ((x58 ≤ x18) ∧ (x18 ≤ x15) ∧ ((x15 - x58) ≥ 1) ∧ ((x15 - x18) ≤ (t - 1)) ∧ ((x18 - x58) ≤ (t - 1))))) : (((x18 - x15) ≤ (t - 1)) ∨ ((x15 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9703 (t x15 x18 x58 : ℝ) (h : (((x15 ≤ x18) ∧ (x18 ≤ x58) ∧ ((x58 - x15) ≥ 1) ∧ ((x18 - x15) ≤ (t - 1)) ∧ ((x58 - x18) ≤ (t - 1))) ∨ ((x58 ≤ x18) ∧ (x18 ≤ x15) ∧ ((x15 - x58) ≥ 1) ∧ ((x15 - x18) ≤ (t - 1)) ∧ ((x18 - x58) ≤ (t - 1))))) : (((x18 - x15) ≤ (t - 1)) ∨ ((x18 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9704 (t x15 x18 x58 : ℝ) (h : (((x15 ≤ x18) ∧ (x18 ≤ x58) ∧ ((x58 - x15) ≥ 1) ∧ ((x18 - x15) ≤ (t - 1)) ∧ ((x58 - x18) ≤ (t - 1))) ∨ ((x58 ≤ x18) ∧ (x18 ≤ x15) ∧ ((x15 - x58) ≥ 1) ∧ ((x15 - x18) ≤ (t - 1)) ∧ ((x18 - x58) ≤ (t - 1))))) : (((x58 - x18) ≤ (t - 1)) ∨ (x58 ≤ x18)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x18) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x18) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9705 (t x15 x18 x58 : ℝ) (h : (((x15 ≤ x18) ∧ (x18 ≤ x58) ∧ ((x58 - x15) ≥ 1) ∧ ((x18 - x15) ≤ (t - 1)) ∧ ((x58 - x18) ≤ (t - 1))) ∨ ((x58 ≤ x18) ∧ (x18 ≤ x15) ∧ ((x15 - x58) ≥ 1) ∧ ((x15 - x18) ≤ (t - 1)) ∧ ((x18 - x58) ≤ (t - 1))))) : (((x58 - x18) ≤ (t - 1)) ∨ (x18 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x18) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9706 (t x15 x18 x58 : ℝ) (h : (((x15 ≤ x18) ∧ (x18 ≤ x58) ∧ ((x58 - x15) ≥ 1) ∧ ((x18 - x15) ≤ (t - 1)) ∧ ((x58 - x18) ≤ (t - 1))) ∨ ((x58 ≤ x18) ∧ (x18 ≤ x15) ∧ ((x15 - x58) ≥ 1) ∧ ((x15 - x18) ≤ (t - 1)) ∧ ((x18 - x58) ≤ (t - 1))))) : (((x58 - x18) ≤ (t - 1)) ∨ ((x15 - x58) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x18) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x58) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9707 (t x15 x18 x58 : ℝ) (h : (((x15 ≤ x18) ∧ (x18 ≤ x58) ∧ ((x58 - x15) ≥ 1) ∧ ((x18 - x15) ≤ (t - 1)) ∧ ((x58 - x18) ≤ (t - 1))) ∨ ((x58 ≤ x18) ∧ (x18 ≤ x15) ∧ ((x15 - x58) ≥ 1) ∧ ((x15 - x18) ≤ (t - 1)) ∧ ((x18 - x58) ≤ (t - 1))))) : (((x58 - x18) ≤ (t - 1)) ∨ ((x15 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x18) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9708 (t x15 x18 x58 : ℝ) (h : (((x15 ≤ x18) ∧ (x18 ≤ x58) ∧ ((x58 - x15) ≥ 1) ∧ ((x18 - x15) ≤ (t - 1)) ∧ ((x58 - x18) ≤ (t - 1))) ∨ ((x58 ≤ x18) ∧ (x18 ≤ x15) ∧ ((x15 - x58) ≥ 1) ∧ ((x15 - x18) ≤ (t - 1)) ∧ ((x18 - x58) ≤ (t - 1))))) : (((x58 - x18) ≤ (t - 1)) ∨ ((x18 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x18) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9710 (x04 x14 x34 x45 : ℝ) : ((¬ ((x14 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0))) := by
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
  have u2 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th982 x04 x14 x34 x45
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u0 (And.intro u3 u2)))) h

theorem clause9711 (t x24 x34 x35 x45 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((t + x24 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x58)) ≤ (-1)))) := by
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
  have u4 : ((x35 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th983 t x24 x34 x35 x45 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u3 (And.intro u4 (And.intro u2 u0))))))) h

theorem clause9719 (t x25 x28 x58 : ℝ) : (((x25 + ((-1) * x58)) ≥ 1) ∨ ((x28 + ((-1) * x58)) ≤ 0) ∨ (¬ (x25 ≤ x28)) ∨ (¬ (x28 ≤ x58)) ∨ (¬ ((x58 - x25) ≥ 1)) ∨ (¬ ((x28 - x25) ≤ (t - 1))) ∨ (¬ ((x58 - x28) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x58)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 + ((-1) * x58)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x58 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x28 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th985 t x25 x28 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9722 (t x25 x28 x58 : ℝ) : (((x25 + ((-1) * x58)) ≤ (-1)) ∨ ((x28 + ((-1) * x58)) ≥ 0) ∨ (¬ (x25 ≤ x28)) ∨ (¬ (x28 ≤ x58)) ∨ (¬ ((x58 - x25) ≥ 1)) ∨ (¬ ((x28 - x25) ≤ (t - 1))) ∨ (¬ ((x58 - x28) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x58)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 + ((-1) * x58)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x58 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x28 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th985 t x25 x28 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9724 (t x25 x28 x58 : ℝ) : (((x25 + ((-1) * x58)) ≥ 1) ∨ ((x25 + ((-1) * x58)) ≤ (-1)) ∨ (¬ (x25 ≤ x28)) ∨ (¬ (x28 ≤ x58)) ∨ (¬ ((x58 - x25) ≥ 1)) ∨ (¬ ((x28 - x25) ≤ (t - 1))) ∨ (¬ ((x58 - x28) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x58)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x58)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x58 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x28 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th985 t x25 x28 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9744 (t x25 x28 x58 : ℝ) : (((x25 + ((-1) * x58)) ≥ 1) ∨ ((x28 + ((-1) * x58)) ≤ 0) ∨ (¬ (x58 ≤ x28)) ∨ (¬ (x28 ≤ x25)) ∨ (¬ ((x25 - x58) ≥ 1)) ∨ (¬ ((x25 - x28) ≤ (t - 1))) ∨ (¬ ((x28 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x58)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 + ((-1) * x58)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x58 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x58) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x28 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th985 t x25 x28 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9747 (t x25 x28 x58 : ℝ) : (((x25 + ((-1) * x58)) ≤ (-1)) ∨ ((x28 + ((-1) * x58)) ≥ 0) ∨ (¬ (x58 ≤ x28)) ∨ (¬ (x28 ≤ x25)) ∨ (¬ ((x25 - x58) ≥ 1)) ∨ (¬ ((x25 - x28) ≤ (t - 1))) ∨ (¬ ((x28 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x58)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 + ((-1) * x58)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x58 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x58) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x28 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th985 t x25 x28 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9749 (t x25 x28 x58 : ℝ) : (((x25 + ((-1) * x58)) ≥ 1) ∨ ((x25 + ((-1) * x58)) ≤ (-1)) ∨ (¬ (x58 ≤ x28)) ∨ (¬ (x28 ≤ x25)) ∨ (¬ ((x25 - x58) ≥ 1)) ∨ (¬ ((x25 - x28) ≤ (t - 1))) ∨ (¬ ((x28 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x58)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x58)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x58 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x58) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x28 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th985 t x25 x28 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9812 (t x25 x28 x58 : ℝ) (h : (((x25 ≤ x28) ∧ (x28 ≤ x58) ∧ ((x58 - x25) ≥ 1) ∧ ((x28 - x25) ≤ (t - 1)) ∧ ((x58 - x28) ≤ (t - 1))) ∨ ((x58 ≤ x28) ∧ (x28 ≤ x25) ∧ ((x25 - x58) ≥ 1) ∧ ((x25 - x28) ≤ (t - 1)) ∧ ((x28 - x58) ≤ (t - 1))))) : ((x25 ≤ x28) ∨ (x58 ≤ x28)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x28) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9813 (t x25 x28 x58 : ℝ) (h : (((x25 ≤ x28) ∧ (x28 ≤ x58) ∧ ((x58 - x25) ≥ 1) ∧ ((x28 - x25) ≤ (t - 1)) ∧ ((x58 - x28) ≤ (t - 1))) ∨ ((x58 ≤ x28) ∧ (x28 ≤ x25) ∧ ((x25 - x58) ≥ 1) ∧ ((x25 - x28) ≤ (t - 1)) ∧ ((x28 - x58) ≤ (t - 1))))) : ((x25 ≤ x28) ∨ (x28 ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x25) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9814 (t x25 x28 x58 : ℝ) (h : (((x25 ≤ x28) ∧ (x28 ≤ x58) ∧ ((x58 - x25) ≥ 1) ∧ ((x28 - x25) ≤ (t - 1)) ∧ ((x58 - x28) ≤ (t - 1))) ∨ ((x58 ≤ x28) ∧ (x28 ≤ x25) ∧ ((x25 - x58) ≥ 1) ∧ ((x25 - x28) ≤ (t - 1)) ∧ ((x28 - x58) ≤ (t - 1))))) : ((x25 ≤ x28) ∨ ((x25 - x58) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x58) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9815 (t x25 x28 x58 : ℝ) (h : (((x25 ≤ x28) ∧ (x28 ≤ x58) ∧ ((x58 - x25) ≥ 1) ∧ ((x28 - x25) ≤ (t - 1)) ∧ ((x58 - x28) ≤ (t - 1))) ∨ ((x58 ≤ x28) ∧ (x28 ≤ x25) ∧ ((x25 - x58) ≥ 1) ∧ ((x25 - x28) ≤ (t - 1)) ∧ ((x28 - x58) ≤ (t - 1))))) : ((x25 ≤ x28) ∨ ((x25 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9816 (t x25 x28 x58 : ℝ) (h : (((x25 ≤ x28) ∧ (x28 ≤ x58) ∧ ((x58 - x25) ≥ 1) ∧ ((x28 - x25) ≤ (t - 1)) ∧ ((x58 - x28) ≤ (t - 1))) ∨ ((x58 ≤ x28) ∧ (x28 ≤ x25) ∧ ((x25 - x58) ≥ 1) ∧ ((x25 - x28) ≤ (t - 1)) ∧ ((x28 - x58) ≤ (t - 1))))) : ((x25 ≤ x28) ∨ ((x28 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9817 (t x25 x28 x58 : ℝ) (h : (((x25 ≤ x28) ∧ (x28 ≤ x58) ∧ ((x58 - x25) ≥ 1) ∧ ((x28 - x25) ≤ (t - 1)) ∧ ((x58 - x28) ≤ (t - 1))) ∨ ((x58 ≤ x28) ∧ (x28 ≤ x25) ∧ ((x25 - x58) ≥ 1) ∧ ((x25 - x28) ≤ (t - 1)) ∧ ((x28 - x58) ≤ (t - 1))))) : ((x28 ≤ x58) ∨ (x58 ≤ x28)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x28 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x28) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9818 (t x25 x28 x58 : ℝ) (h : (((x25 ≤ x28) ∧ (x28 ≤ x58) ∧ ((x58 - x25) ≥ 1) ∧ ((x28 - x25) ≤ (t - 1)) ∧ ((x58 - x28) ≤ (t - 1))) ∨ ((x58 ≤ x28) ∧ (x28 ≤ x25) ∧ ((x25 - x58) ≥ 1) ∧ ((x25 - x28) ≤ (t - 1)) ∧ ((x28 - x58) ≤ (t - 1))))) : ((x28 ≤ x58) ∨ (x28 ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x28 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x25) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9819 (t x25 x28 x58 : ℝ) (h : (((x25 ≤ x28) ∧ (x28 ≤ x58) ∧ ((x58 - x25) ≥ 1) ∧ ((x28 - x25) ≤ (t - 1)) ∧ ((x58 - x28) ≤ (t - 1))) ∨ ((x58 ≤ x28) ∧ (x28 ≤ x25) ∧ ((x25 - x58) ≥ 1) ∧ ((x25 - x28) ≤ (t - 1)) ∧ ((x28 - x58) ≤ (t - 1))))) : ((x28 ≤ x58) ∨ ((x25 - x58) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x28 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x58) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9820 (t x25 x28 x58 : ℝ) (h : (((x25 ≤ x28) ∧ (x28 ≤ x58) ∧ ((x58 - x25) ≥ 1) ∧ ((x28 - x25) ≤ (t - 1)) ∧ ((x58 - x28) ≤ (t - 1))) ∨ ((x58 ≤ x28) ∧ (x28 ≤ x25) ∧ ((x25 - x58) ≥ 1) ∧ ((x25 - x28) ≤ (t - 1)) ∧ ((x28 - x58) ≤ (t - 1))))) : ((x28 ≤ x58) ∨ ((x25 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x28 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9821 (t x25 x28 x58 : ℝ) (h : (((x25 ≤ x28) ∧ (x28 ≤ x58) ∧ ((x58 - x25) ≥ 1) ∧ ((x28 - x25) ≤ (t - 1)) ∧ ((x58 - x28) ≤ (t - 1))) ∨ ((x58 ≤ x28) ∧ (x28 ≤ x25) ∧ ((x25 - x58) ≥ 1) ∧ ((x25 - x28) ≤ (t - 1)) ∧ ((x28 - x58) ≤ (t - 1))))) : ((x28 ≤ x58) ∨ ((x28 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x28 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9822 (t x25 x28 x58 : ℝ) (h : (((x25 ≤ x28) ∧ (x28 ≤ x58) ∧ ((x58 - x25) ≥ 1) ∧ ((x28 - x25) ≤ (t - 1)) ∧ ((x58 - x28) ≤ (t - 1))) ∨ ((x58 ≤ x28) ∧ (x28 ≤ x25) ∧ ((x25 - x58) ≥ 1) ∧ ((x25 - x28) ≤ (t - 1)) ∧ ((x28 - x58) ≤ (t - 1))))) : (((x58 - x25) ≥ 1) ∨ (x58 ≤ x28)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x25) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x28) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9823 (t x25 x28 x58 : ℝ) (h : (((x25 ≤ x28) ∧ (x28 ≤ x58) ∧ ((x58 - x25) ≥ 1) ∧ ((x28 - x25) ≤ (t - 1)) ∧ ((x58 - x28) ≤ (t - 1))) ∨ ((x58 ≤ x28) ∧ (x28 ≤ x25) ∧ ((x25 - x58) ≥ 1) ∧ ((x25 - x28) ≤ (t - 1)) ∧ ((x28 - x58) ≤ (t - 1))))) : (((x58 - x25) ≥ 1) ∨ (x28 ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x25) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x25) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9824 (t x25 x28 x58 : ℝ) (h : (((x25 ≤ x28) ∧ (x28 ≤ x58) ∧ ((x58 - x25) ≥ 1) ∧ ((x28 - x25) ≤ (t - 1)) ∧ ((x58 - x28) ≤ (t - 1))) ∨ ((x58 ≤ x28) ∧ (x28 ≤ x25) ∧ ((x25 - x58) ≥ 1) ∧ ((x25 - x28) ≤ (t - 1)) ∧ ((x28 - x58) ≤ (t - 1))))) : (((x58 - x25) ≥ 1) ∨ ((x25 - x58) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x25) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x58) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9825 (t x25 x28 x58 : ℝ) (h : (((x25 ≤ x28) ∧ (x28 ≤ x58) ∧ ((x58 - x25) ≥ 1) ∧ ((x28 - x25) ≤ (t - 1)) ∧ ((x58 - x28) ≤ (t - 1))) ∨ ((x58 ≤ x28) ∧ (x28 ≤ x25) ∧ ((x25 - x58) ≥ 1) ∧ ((x25 - x28) ≤ (t - 1)) ∧ ((x28 - x58) ≤ (t - 1))))) : (((x58 - x25) ≥ 1) ∨ ((x25 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x25) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9826 (t x25 x28 x58 : ℝ) (h : (((x25 ≤ x28) ∧ (x28 ≤ x58) ∧ ((x58 - x25) ≥ 1) ∧ ((x28 - x25) ≤ (t - 1)) ∧ ((x58 - x28) ≤ (t - 1))) ∨ ((x58 ≤ x28) ∧ (x28 ≤ x25) ∧ ((x25 - x58) ≥ 1) ∧ ((x25 - x28) ≤ (t - 1)) ∧ ((x28 - x58) ≤ (t - 1))))) : (((x58 - x25) ≥ 1) ∨ ((x28 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x25) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9827 (t x25 x28 x58 : ℝ) (h : (((x25 ≤ x28) ∧ (x28 ≤ x58) ∧ ((x58 - x25) ≥ 1) ∧ ((x28 - x25) ≤ (t - 1)) ∧ ((x58 - x28) ≤ (t - 1))) ∨ ((x58 ≤ x28) ∧ (x28 ≤ x25) ∧ ((x25 - x58) ≥ 1) ∧ ((x25 - x28) ≤ (t - 1)) ∧ ((x28 - x58) ≤ (t - 1))))) : (((x28 - x25) ≤ (t - 1)) ∨ (x58 ≤ x28)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x25) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x28) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9828 (t x25 x28 x58 : ℝ) (h : (((x25 ≤ x28) ∧ (x28 ≤ x58) ∧ ((x58 - x25) ≥ 1) ∧ ((x28 - x25) ≤ (t - 1)) ∧ ((x58 - x28) ≤ (t - 1))) ∨ ((x58 ≤ x28) ∧ (x28 ≤ x25) ∧ ((x25 - x58) ≥ 1) ∧ ((x25 - x28) ≤ (t - 1)) ∧ ((x28 - x58) ≤ (t - 1))))) : (((x28 - x25) ≤ (t - 1)) ∨ (x28 ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x25) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x25) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9829 (t x25 x28 x58 : ℝ) (h : (((x25 ≤ x28) ∧ (x28 ≤ x58) ∧ ((x58 - x25) ≥ 1) ∧ ((x28 - x25) ≤ (t - 1)) ∧ ((x58 - x28) ≤ (t - 1))) ∨ ((x58 ≤ x28) ∧ (x28 ≤ x25) ∧ ((x25 - x58) ≥ 1) ∧ ((x25 - x28) ≤ (t - 1)) ∧ ((x28 - x58) ≤ (t - 1))))) : (((x28 - x25) ≤ (t - 1)) ∨ ((x25 - x58) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x25) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x58) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9830 (t x25 x28 x58 : ℝ) (h : (((x25 ≤ x28) ∧ (x28 ≤ x58) ∧ ((x58 - x25) ≥ 1) ∧ ((x28 - x25) ≤ (t - 1)) ∧ ((x58 - x28) ≤ (t - 1))) ∨ ((x58 ≤ x28) ∧ (x28 ≤ x25) ∧ ((x25 - x58) ≥ 1) ∧ ((x25 - x28) ≤ (t - 1)) ∧ ((x28 - x58) ≤ (t - 1))))) : (((x28 - x25) ≤ (t - 1)) ∨ ((x25 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x25) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9831 (t x25 x28 x58 : ℝ) (h : (((x25 ≤ x28) ∧ (x28 ≤ x58) ∧ ((x58 - x25) ≥ 1) ∧ ((x28 - x25) ≤ (t - 1)) ∧ ((x58 - x28) ≤ (t - 1))) ∨ ((x58 ≤ x28) ∧ (x28 ≤ x25) ∧ ((x25 - x58) ≥ 1) ∧ ((x25 - x28) ≤ (t - 1)) ∧ ((x28 - x58) ≤ (t - 1))))) : (((x28 - x25) ≤ (t - 1)) ∨ ((x28 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x25) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9832 (t x25 x28 x58 : ℝ) (h : (((x25 ≤ x28) ∧ (x28 ≤ x58) ∧ ((x58 - x25) ≥ 1) ∧ ((x28 - x25) ≤ (t - 1)) ∧ ((x58 - x28) ≤ (t - 1))) ∨ ((x58 ≤ x28) ∧ (x28 ≤ x25) ∧ ((x25 - x58) ≥ 1) ∧ ((x25 - x28) ≤ (t - 1)) ∧ ((x28 - x58) ≤ (t - 1))))) : (((x58 - x28) ≤ (t - 1)) ∨ (x58 ≤ x28)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x28) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x28) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9833 (t x25 x28 x58 : ℝ) (h : (((x25 ≤ x28) ∧ (x28 ≤ x58) ∧ ((x58 - x25) ≥ 1) ∧ ((x28 - x25) ≤ (t - 1)) ∧ ((x58 - x28) ≤ (t - 1))) ∨ ((x58 ≤ x28) ∧ (x28 ≤ x25) ∧ ((x25 - x58) ≥ 1) ∧ ((x25 - x28) ≤ (t - 1)) ∧ ((x28 - x58) ≤ (t - 1))))) : (((x58 - x28) ≤ (t - 1)) ∨ (x28 ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x28) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x25) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9834 (t x25 x28 x58 : ℝ) (h : (((x25 ≤ x28) ∧ (x28 ≤ x58) ∧ ((x58 - x25) ≥ 1) ∧ ((x28 - x25) ≤ (t - 1)) ∧ ((x58 - x28) ≤ (t - 1))) ∨ ((x58 ≤ x28) ∧ (x28 ≤ x25) ∧ ((x25 - x58) ≥ 1) ∧ ((x25 - x28) ≤ (t - 1)) ∧ ((x28 - x58) ≤ (t - 1))))) : (((x58 - x28) ≤ (t - 1)) ∨ ((x25 - x58) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x28) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x58) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9835 (t x25 x28 x58 : ℝ) (h : (((x25 ≤ x28) ∧ (x28 ≤ x58) ∧ ((x58 - x25) ≥ 1) ∧ ((x28 - x25) ≤ (t - 1)) ∧ ((x58 - x28) ≤ (t - 1))) ∨ ((x58 ≤ x28) ∧ (x28 ≤ x25) ∧ ((x25 - x58) ≥ 1) ∧ ((x25 - x28) ≤ (t - 1)) ∧ ((x28 - x58) ≤ (t - 1))))) : (((x58 - x28) ≤ (t - 1)) ∨ ((x25 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x28) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9836 (t x25 x28 x58 : ℝ) (h : (((x25 ≤ x28) ∧ (x28 ≤ x58) ∧ ((x58 - x25) ≥ 1) ∧ ((x28 - x25) ≤ (t - 1)) ∧ ((x58 - x28) ≤ (t - 1))) ∨ ((x58 ≤ x28) ∧ (x28 ≤ x25) ∧ ((x25 - x58) ≥ 1) ∧ ((x25 - x28) ≤ (t - 1)) ∧ ((x28 - x58) ≤ (t - 1))))) : (((x58 - x28) ≤ (t - 1)) ∨ ((x28 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x28) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9837 (x58 : ℝ) (h : (x58 ≥ 0)) : ((x58 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x58 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause9838 (t x03 x13 x35 : ℝ) : (((t + x03 + ((-1) * x13)) ≥ 1) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ ((t + ((-1) * x35)) ≤ 0) ∨ (¬ (x03 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x03 + ((-1) * x13)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th994 t x03 x13 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u1 u3))))) h

theorem clause9840 (x05 x15 x57 : ℝ) : ((¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x15)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th998 x05 x15 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 u1)))) h

theorem clause9844 (t x01 x04 x13 x14 x15 x24 x45 x46 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + x13 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0)) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x13 + ((-1) * x14)) ≥ 1) := by
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
  have u5 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th1009 t x01 x04 x13 x14 x15 x24 x45 x46 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u8 (And.intro u0 (And.intro u10 (And.intro u1 (And.intro u2 (And.intro u5 (And.intro u6 (And.intro u4 (And.intro u3 u9)))))))))))) h

theorem clause9845 (x02 x04 x05 : ℝ) : (((x02 + ((-1) * x05)) ≥ 0) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x05)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x05)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1010 x02 x04 x05
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause9846 (x14 x24 x46 : ℝ) : ((¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x24)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1013 x14 x24 x46
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 u0))) h

theorem clause9847 (t x01 x15 x16 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((t + ((-1) * x15) + x45) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x15) + x45) ≥ 1) := by
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
  have h := NineTheoryTrial.th1018 t x01 x15 x16 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u5 (And.intro u1 (And.intro u3 u4))))))) h

theorem clause9848 (x01 x15 x16 : ℝ) : ((¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x16)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x15 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1019 x01 x15 x16
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u0 u2))) h

theorem clause9856 (t x14 x18 x48 : ℝ) : (((x18 + ((-1) * x48)) ≤ 0) ∨ ((x14 + ((-1) * x48)) ≥ 1) ∨ (¬ (x14 ≤ x18)) ∨ (¬ (x18 ≤ x48)) ∨ (¬ ((x48 - x14) ≥ 1)) ∨ (¬ ((x18 - x14) ≤ (t - 1))) ∨ (¬ ((x48 - x18) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 + ((-1) * x48)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x48)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x18) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x18 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x48 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x18 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x18) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1023 t x14 x18 x48
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9861 (t x14 x18 x48 : ℝ) : (((x14 + ((-1) * x48)) ≤ (-1)) ∨ ((x14 + ((-1) * x48)) ≥ 1) ∨ (¬ (x14 ≤ x18)) ∨ (¬ (x18 ≤ x48)) ∨ (¬ ((x48 - x14) ≥ 1)) ∨ (¬ ((x18 - x14) ≤ (t - 1))) ∨ (¬ ((x48 - x18) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x48)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x48)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x18) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x18 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x48 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x18 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x18) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1023 t x14 x18 x48
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9881 (t x14 x18 x48 : ℝ) : (((x18 + ((-1) * x48)) ≤ 0) ∨ ((x14 + ((-1) * x48)) ≥ 1) ∨ (¬ (x48 ≤ x18)) ∨ (¬ (x18 ≤ x14)) ∨ (¬ ((x14 - x48) ≥ 1)) ∨ (¬ ((x14 - x18) ≤ (t - 1))) ∨ (¬ ((x18 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 + ((-1) * x48)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x48)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x48 ≤ x18) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x18 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x48) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x18) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x18 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1023 t x14 x18 x48
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9886 (t x14 x18 x48 : ℝ) : (((x14 + ((-1) * x48)) ≤ (-1)) ∨ ((x14 + ((-1) * x48)) ≥ 1) ∨ (¬ (x48 ≤ x18)) ∨ (¬ (x18 ≤ x14)) ∨ (¬ ((x14 - x48) ≥ 1)) ∨ (¬ ((x14 - x18) ≤ (t - 1))) ∨ (¬ ((x18 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x48)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x48)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x48 ≤ x18) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x18 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x48) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x18) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x18 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1023 t x14 x18 x48
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9949 (t x14 x18 x48 : ℝ) (h : (((x14 ≤ x18) ∧ (x18 ≤ x48) ∧ ((x48 - x14) ≥ 1) ∧ ((x18 - x14) ≤ (t - 1)) ∧ ((x48 - x18) ≤ (t - 1))) ∨ ((x48 ≤ x18) ∧ (x18 ≤ x14) ∧ ((x14 - x48) ≥ 1) ∧ ((x14 - x18) ≤ (t - 1)) ∧ ((x18 - x48) ≤ (t - 1))))) : ((x14 ≤ x18) ∨ (x48 ≤ x18)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x18) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9950 (t x14 x18 x48 : ℝ) (h : (((x14 ≤ x18) ∧ (x18 ≤ x48) ∧ ((x48 - x14) ≥ 1) ∧ ((x18 - x14) ≤ (t - 1)) ∧ ((x48 - x18) ≤ (t - 1))) ∨ ((x48 ≤ x18) ∧ (x18 ≤ x14) ∧ ((x14 - x48) ≥ 1) ∧ ((x14 - x18) ≤ (t - 1)) ∧ ((x18 - x48) ≤ (t - 1))))) : ((x14 ≤ x18) ∨ (x18 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9951 (t x14 x18 x48 : ℝ) (h : (((x14 ≤ x18) ∧ (x18 ≤ x48) ∧ ((x48 - x14) ≥ 1) ∧ ((x18 - x14) ≤ (t - 1)) ∧ ((x48 - x18) ≤ (t - 1))) ∨ ((x48 ≤ x18) ∧ (x18 ≤ x14) ∧ ((x14 - x48) ≥ 1) ∧ ((x14 - x18) ≤ (t - 1)) ∧ ((x18 - x48) ≤ (t - 1))))) : ((x14 ≤ x18) ∨ ((x14 - x48) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x48) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9952 (t x14 x18 x48 : ℝ) (h : (((x14 ≤ x18) ∧ (x18 ≤ x48) ∧ ((x48 - x14) ≥ 1) ∧ ((x18 - x14) ≤ (t - 1)) ∧ ((x48 - x18) ≤ (t - 1))) ∨ ((x48 ≤ x18) ∧ (x18 ≤ x14) ∧ ((x14 - x48) ≥ 1) ∧ ((x14 - x18) ≤ (t - 1)) ∧ ((x18 - x48) ≤ (t - 1))))) : ((x14 ≤ x18) ∨ ((x14 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9953 (t x14 x18 x48 : ℝ) (h : (((x14 ≤ x18) ∧ (x18 ≤ x48) ∧ ((x48 - x14) ≥ 1) ∧ ((x18 - x14) ≤ (t - 1)) ∧ ((x48 - x18) ≤ (t - 1))) ∨ ((x48 ≤ x18) ∧ (x18 ≤ x14) ∧ ((x14 - x48) ≥ 1) ∧ ((x14 - x18) ≤ (t - 1)) ∧ ((x18 - x48) ≤ (t - 1))))) : ((x14 ≤ x18) ∨ ((x18 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9954 (t x14 x18 x48 : ℝ) (h : (((x14 ≤ x18) ∧ (x18 ≤ x48) ∧ ((x48 - x14) ≥ 1) ∧ ((x18 - x14) ≤ (t - 1)) ∧ ((x48 - x18) ≤ (t - 1))) ∨ ((x48 ≤ x18) ∧ (x18 ≤ x14) ∧ ((x14 - x48) ≥ 1) ∧ ((x14 - x18) ≤ (t - 1)) ∧ ((x18 - x48) ≤ (t - 1))))) : ((x18 ≤ x48) ∨ (x48 ≤ x18)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x18 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x18) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9955 (t x14 x18 x48 : ℝ) (h : (((x14 ≤ x18) ∧ (x18 ≤ x48) ∧ ((x48 - x14) ≥ 1) ∧ ((x18 - x14) ≤ (t - 1)) ∧ ((x48 - x18) ≤ (t - 1))) ∨ ((x48 ≤ x18) ∧ (x18 ≤ x14) ∧ ((x14 - x48) ≥ 1) ∧ ((x14 - x18) ≤ (t - 1)) ∧ ((x18 - x48) ≤ (t - 1))))) : ((x18 ≤ x48) ∨ (x18 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x18 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9956 (t x14 x18 x48 : ℝ) (h : (((x14 ≤ x18) ∧ (x18 ≤ x48) ∧ ((x48 - x14) ≥ 1) ∧ ((x18 - x14) ≤ (t - 1)) ∧ ((x48 - x18) ≤ (t - 1))) ∨ ((x48 ≤ x18) ∧ (x18 ≤ x14) ∧ ((x14 - x48) ≥ 1) ∧ ((x14 - x18) ≤ (t - 1)) ∧ ((x18 - x48) ≤ (t - 1))))) : ((x18 ≤ x48) ∨ ((x14 - x48) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x18 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x48) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9957 (t x14 x18 x48 : ℝ) (h : (((x14 ≤ x18) ∧ (x18 ≤ x48) ∧ ((x48 - x14) ≥ 1) ∧ ((x18 - x14) ≤ (t - 1)) ∧ ((x48 - x18) ≤ (t - 1))) ∨ ((x48 ≤ x18) ∧ (x18 ≤ x14) ∧ ((x14 - x48) ≥ 1) ∧ ((x14 - x18) ≤ (t - 1)) ∧ ((x18 - x48) ≤ (t - 1))))) : ((x18 ≤ x48) ∨ ((x14 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x18 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9958 (t x14 x18 x48 : ℝ) (h : (((x14 ≤ x18) ∧ (x18 ≤ x48) ∧ ((x48 - x14) ≥ 1) ∧ ((x18 - x14) ≤ (t - 1)) ∧ ((x48 - x18) ≤ (t - 1))) ∨ ((x48 ≤ x18) ∧ (x18 ≤ x14) ∧ ((x14 - x48) ≥ 1) ∧ ((x14 - x18) ≤ (t - 1)) ∧ ((x18 - x48) ≤ (t - 1))))) : ((x18 ≤ x48) ∨ ((x18 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x18 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9959 (t x14 x18 x48 : ℝ) (h : (((x14 ≤ x18) ∧ (x18 ≤ x48) ∧ ((x48 - x14) ≥ 1) ∧ ((x18 - x14) ≤ (t - 1)) ∧ ((x48 - x18) ≤ (t - 1))) ∨ ((x48 ≤ x18) ∧ (x18 ≤ x14) ∧ ((x14 - x48) ≥ 1) ∧ ((x14 - x18) ≤ (t - 1)) ∧ ((x18 - x48) ≤ (t - 1))))) : (((x48 - x14) ≥ 1) ∨ (x48 ≤ x18)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x14) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x18) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9960 (t x14 x18 x48 : ℝ) (h : (((x14 ≤ x18) ∧ (x18 ≤ x48) ∧ ((x48 - x14) ≥ 1) ∧ ((x18 - x14) ≤ (t - 1)) ∧ ((x48 - x18) ≤ (t - 1))) ∨ ((x48 ≤ x18) ∧ (x18 ≤ x14) ∧ ((x14 - x48) ≥ 1) ∧ ((x14 - x18) ≤ (t - 1)) ∧ ((x18 - x48) ≤ (t - 1))))) : (((x48 - x14) ≥ 1) ∨ (x18 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x14) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9961 (t x14 x18 x48 : ℝ) (h : (((x14 ≤ x18) ∧ (x18 ≤ x48) ∧ ((x48 - x14) ≥ 1) ∧ ((x18 - x14) ≤ (t - 1)) ∧ ((x48 - x18) ≤ (t - 1))) ∨ ((x48 ≤ x18) ∧ (x18 ≤ x14) ∧ ((x14 - x48) ≥ 1) ∧ ((x14 - x18) ≤ (t - 1)) ∧ ((x18 - x48) ≤ (t - 1))))) : (((x48 - x14) ≥ 1) ∨ ((x14 - x48) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x14) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x48) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9962 (t x14 x18 x48 : ℝ) (h : (((x14 ≤ x18) ∧ (x18 ≤ x48) ∧ ((x48 - x14) ≥ 1) ∧ ((x18 - x14) ≤ (t - 1)) ∧ ((x48 - x18) ≤ (t - 1))) ∨ ((x48 ≤ x18) ∧ (x18 ≤ x14) ∧ ((x14 - x48) ≥ 1) ∧ ((x14 - x18) ≤ (t - 1)) ∧ ((x18 - x48) ≤ (t - 1))))) : (((x48 - x14) ≥ 1) ∨ ((x14 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x14) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9963 (t x14 x18 x48 : ℝ) (h : (((x14 ≤ x18) ∧ (x18 ≤ x48) ∧ ((x48 - x14) ≥ 1) ∧ ((x18 - x14) ≤ (t - 1)) ∧ ((x48 - x18) ≤ (t - 1))) ∨ ((x48 ≤ x18) ∧ (x18 ≤ x14) ∧ ((x14 - x48) ≥ 1) ∧ ((x14 - x18) ≤ (t - 1)) ∧ ((x18 - x48) ≤ (t - 1))))) : (((x48 - x14) ≥ 1) ∨ ((x18 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x14) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9964 (t x14 x18 x48 : ℝ) (h : (((x14 ≤ x18) ∧ (x18 ≤ x48) ∧ ((x48 - x14) ≥ 1) ∧ ((x18 - x14) ≤ (t - 1)) ∧ ((x48 - x18) ≤ (t - 1))) ∨ ((x48 ≤ x18) ∧ (x18 ≤ x14) ∧ ((x14 - x48) ≥ 1) ∧ ((x14 - x18) ≤ (t - 1)) ∧ ((x18 - x48) ≤ (t - 1))))) : (((x18 - x14) ≤ (t - 1)) ∨ (x48 ≤ x18)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x18) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9965 (t x14 x18 x48 : ℝ) (h : (((x14 ≤ x18) ∧ (x18 ≤ x48) ∧ ((x48 - x14) ≥ 1) ∧ ((x18 - x14) ≤ (t - 1)) ∧ ((x48 - x18) ≤ (t - 1))) ∨ ((x48 ≤ x18) ∧ (x18 ≤ x14) ∧ ((x14 - x48) ≥ 1) ∧ ((x14 - x18) ≤ (t - 1)) ∧ ((x18 - x48) ≤ (t - 1))))) : (((x18 - x14) ≤ (t - 1)) ∨ (x18 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9966 (t x14 x18 x48 : ℝ) (h : (((x14 ≤ x18) ∧ (x18 ≤ x48) ∧ ((x48 - x14) ≥ 1) ∧ ((x18 - x14) ≤ (t - 1)) ∧ ((x48 - x18) ≤ (t - 1))) ∨ ((x48 ≤ x18) ∧ (x18 ≤ x14) ∧ ((x14 - x48) ≥ 1) ∧ ((x14 - x18) ≤ (t - 1)) ∧ ((x18 - x48) ≤ (t - 1))))) : (((x18 - x14) ≤ (t - 1)) ∨ ((x14 - x48) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x48) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9967 (t x14 x18 x48 : ℝ) (h : (((x14 ≤ x18) ∧ (x18 ≤ x48) ∧ ((x48 - x14) ≥ 1) ∧ ((x18 - x14) ≤ (t - 1)) ∧ ((x48 - x18) ≤ (t - 1))) ∨ ((x48 ≤ x18) ∧ (x18 ≤ x14) ∧ ((x14 - x48) ≥ 1) ∧ ((x14 - x18) ≤ (t - 1)) ∧ ((x18 - x48) ≤ (t - 1))))) : (((x18 - x14) ≤ (t - 1)) ∨ ((x14 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9968 (t x14 x18 x48 : ℝ) (h : (((x14 ≤ x18) ∧ (x18 ≤ x48) ∧ ((x48 - x14) ≥ 1) ∧ ((x18 - x14) ≤ (t - 1)) ∧ ((x48 - x18) ≤ (t - 1))) ∨ ((x48 ≤ x18) ∧ (x18 ≤ x14) ∧ ((x14 - x48) ≥ 1) ∧ ((x14 - x18) ≤ (t - 1)) ∧ ((x18 - x48) ≤ (t - 1))))) : (((x18 - x14) ≤ (t - 1)) ∨ ((x18 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9969 (t x14 x18 x48 : ℝ) (h : (((x14 ≤ x18) ∧ (x18 ≤ x48) ∧ ((x48 - x14) ≥ 1) ∧ ((x18 - x14) ≤ (t - 1)) ∧ ((x48 - x18) ≤ (t - 1))) ∨ ((x48 ≤ x18) ∧ (x18 ≤ x14) ∧ ((x14 - x48) ≥ 1) ∧ ((x14 - x18) ≤ (t - 1)) ∧ ((x18 - x48) ≤ (t - 1))))) : (((x48 - x18) ≤ (t - 1)) ∨ (x48 ≤ x18)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x18) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x18) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause9970 (t x14 x18 x48 : ℝ) (h : (((x14 ≤ x18) ∧ (x18 ≤ x48) ∧ ((x48 - x14) ≥ 1) ∧ ((x18 - x14) ≤ (t - 1)) ∧ ((x48 - x18) ≤ (t - 1))) ∨ ((x48 ≤ x18) ∧ (x18 ≤ x14) ∧ ((x14 - x48) ≥ 1) ∧ ((x14 - x18) ≤ (t - 1)) ∧ ((x18 - x48) ≤ (t - 1))))) : (((x48 - x18) ≤ (t - 1)) ∨ (x18 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x18) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause9971 (t x14 x18 x48 : ℝ) (h : (((x14 ≤ x18) ∧ (x18 ≤ x48) ∧ ((x48 - x14) ≥ 1) ∧ ((x18 - x14) ≤ (t - 1)) ∧ ((x48 - x18) ≤ (t - 1))) ∨ ((x48 ≤ x18) ∧ (x18 ≤ x14) ∧ ((x14 - x48) ≥ 1) ∧ ((x14 - x18) ≤ (t - 1)) ∧ ((x18 - x48) ≤ (t - 1))))) : (((x48 - x18) ≤ (t - 1)) ∨ ((x14 - x48) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x18) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x48) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause9972 (t x14 x18 x48 : ℝ) (h : (((x14 ≤ x18) ∧ (x18 ≤ x48) ∧ ((x48 - x14) ≥ 1) ∧ ((x18 - x14) ≤ (t - 1)) ∧ ((x48 - x18) ≤ (t - 1))) ∨ ((x48 ≤ x18) ∧ (x18 ≤ x14) ∧ ((x14 - x48) ≥ 1) ∧ ((x14 - x18) ≤ (t - 1)) ∧ ((x18 - x48) ≤ (t - 1))))) : (((x48 - x18) ≤ (t - 1)) ∨ ((x14 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x18) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause9973 (t x14 x18 x48 : ℝ) (h : (((x14 ≤ x18) ∧ (x18 ≤ x48) ∧ ((x48 - x14) ≥ 1) ∧ ((x18 - x14) ≤ (t - 1)) ∧ ((x48 - x18) ≤ (t - 1))) ∨ ((x48 ≤ x18) ∧ (x18 ≤ x14) ∧ ((x14 - x48) ≥ 1) ∧ ((x14 - x18) ≤ (t - 1)) ∧ ((x18 - x48) ≤ (t - 1))))) : (((x48 - x18) ≤ (t - 1)) ∨ ((x18 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x18) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x18 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause9974 (t x01 x04 x12 x13 x14 x48 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x48)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x48)) ≤ (-1)))) := by
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
  have u3 : ((x01 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1025 t x01 x04 x12 x13 x14 x48
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u6 (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u2 u3)))))))) h

theorem clause9982 (t x04 x08 x48 : ℝ) : (((x08 + ((-1) * x48)) ≤ 0) ∨ ((x04 + ((-1) * x48)) ≥ 1) ∨ (¬ (x04 ≤ x08)) ∨ (¬ (x08 ≤ x48)) ∨ (¬ ((x48 - x04) ≥ 1)) ∨ (¬ ((x08 - x04) ≤ (t - 1))) ∨ (¬ ((x48 - x08) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 + ((-1) * x48)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x48)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≤ x08) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x08 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x48 - x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x08 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x08) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1027 t x04 x08 x48
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause9987 (t x04 x08 x48 : ℝ) : (((x04 + ((-1) * x48)) ≤ (-1)) ∨ ((x04 + ((-1) * x48)) ≥ 1) ∨ (¬ (x04 ≤ x08)) ∨ (¬ (x08 ≤ x48)) ∨ (¬ ((x48 - x04) ≥ 1)) ∨ (¬ ((x08 - x04) ≤ (t - 1))) ∨ (¬ ((x48 - x08) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x48)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x48)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≤ x08) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x08 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x48 - x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x08 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x08) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1027 t x04 x08 x48
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause10007 (t x04 x08 x48 : ℝ) : (((x08 + ((-1) * x48)) ≤ 0) ∨ ((x04 + ((-1) * x48)) ≥ 1) ∨ (¬ (x48 ≤ x08)) ∨ (¬ (x08 ≤ x04)) ∨ (¬ ((x04 - x48) ≥ 1)) ∨ (¬ ((x04 - x08) ≤ (t - 1))) ∨ (¬ ((x08 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 + ((-1) * x48)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x48)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x48 ≤ x08) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x08 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x48) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x08) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x08 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1027 t x04 x08 x48
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause10012 (t x04 x08 x48 : ℝ) : (((x04 + ((-1) * x48)) ≤ (-1)) ∨ ((x04 + ((-1) * x48)) ≥ 1) ∨ (¬ (x48 ≤ x08)) ∨ (¬ (x08 ≤ x04)) ∨ (¬ ((x04 - x48) ≥ 1)) ∨ (¬ ((x04 - x08) ≤ (t - 1))) ∨ (¬ ((x08 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x48)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x48)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x48 ≤ x08) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x08 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x48) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x08) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x08 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1027 t x04 x08 x48
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause10075 (t x04 x08 x48 : ℝ) (h : (((x04 ≤ x08) ∧ (x08 ≤ x48) ∧ ((x48 - x04) ≥ 1) ∧ ((x08 - x04) ≤ (t - 1)) ∧ ((x48 - x08) ≤ (t - 1))) ∨ ((x48 ≤ x08) ∧ (x08 ≤ x04) ∧ ((x04 - x48) ≥ 1) ∧ ((x04 - x08) ≤ (t - 1)) ∧ ((x08 - x48) ≤ (t - 1))))) : ((x04 ≤ x08) ∨ (x48 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause10076 (t x04 x08 x48 : ℝ) (h : (((x04 ≤ x08) ∧ (x08 ≤ x48) ∧ ((x48 - x04) ≥ 1) ∧ ((x08 - x04) ≤ (t - 1)) ∧ ((x48 - x08) ≤ (t - 1))) ∨ ((x48 ≤ x08) ∧ (x08 ≤ x04) ∧ ((x04 - x48) ≥ 1) ∧ ((x04 - x08) ≤ (t - 1)) ∧ ((x08 - x48) ≤ (t - 1))))) : ((x04 ≤ x08) ∨ (x08 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause10077 (t x04 x08 x48 : ℝ) (h : (((x04 ≤ x08) ∧ (x08 ≤ x48) ∧ ((x48 - x04) ≥ 1) ∧ ((x08 - x04) ≤ (t - 1)) ∧ ((x48 - x08) ≤ (t - 1))) ∨ ((x48 ≤ x08) ∧ (x08 ≤ x04) ∧ ((x04 - x48) ≥ 1) ∧ ((x04 - x08) ≤ (t - 1)) ∧ ((x08 - x48) ≤ (t - 1))))) : ((x04 ≤ x08) ∨ ((x04 - x48) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x48) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause10078 (t x04 x08 x48 : ℝ) (h : (((x04 ≤ x08) ∧ (x08 ≤ x48) ∧ ((x48 - x04) ≥ 1) ∧ ((x08 - x04) ≤ (t - 1)) ∧ ((x48 - x08) ≤ (t - 1))) ∨ ((x48 ≤ x08) ∧ (x08 ≤ x04) ∧ ((x04 - x48) ≥ 1) ∧ ((x04 - x08) ≤ (t - 1)) ∧ ((x08 - x48) ≤ (t - 1))))) : ((x04 ≤ x08) ∨ ((x04 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause10079 (t x04 x08 x48 : ℝ) (h : (((x04 ≤ x08) ∧ (x08 ≤ x48) ∧ ((x48 - x04) ≥ 1) ∧ ((x08 - x04) ≤ (t - 1)) ∧ ((x48 - x08) ≤ (t - 1))) ∨ ((x48 ≤ x08) ∧ (x08 ≤ x04) ∧ ((x04 - x48) ≥ 1) ∧ ((x04 - x08) ≤ (t - 1)) ∧ ((x08 - x48) ≤ (t - 1))))) : ((x04 ≤ x08) ∨ ((x08 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause10080 (t x04 x08 x48 : ℝ) (h : (((x04 ≤ x08) ∧ (x08 ≤ x48) ∧ ((x48 - x04) ≥ 1) ∧ ((x08 - x04) ≤ (t - 1)) ∧ ((x48 - x08) ≤ (t - 1))) ∨ ((x48 ≤ x08) ∧ (x08 ≤ x04) ∧ ((x04 - x48) ≥ 1) ∧ ((x04 - x08) ≤ (t - 1)) ∧ ((x08 - x48) ≤ (t - 1))))) : ((x08 ≤ x48) ∨ (x48 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause10081 (t x04 x08 x48 : ℝ) (h : (((x04 ≤ x08) ∧ (x08 ≤ x48) ∧ ((x48 - x04) ≥ 1) ∧ ((x08 - x04) ≤ (t - 1)) ∧ ((x48 - x08) ≤ (t - 1))) ∨ ((x48 ≤ x08) ∧ (x08 ≤ x04) ∧ ((x04 - x48) ≥ 1) ∧ ((x04 - x08) ≤ (t - 1)) ∧ ((x08 - x48) ≤ (t - 1))))) : ((x08 ≤ x48) ∨ (x08 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause10082 (t x04 x08 x48 : ℝ) (h : (((x04 ≤ x08) ∧ (x08 ≤ x48) ∧ ((x48 - x04) ≥ 1) ∧ ((x08 - x04) ≤ (t - 1)) ∧ ((x48 - x08) ≤ (t - 1))) ∨ ((x48 ≤ x08) ∧ (x08 ≤ x04) ∧ ((x04 - x48) ≥ 1) ∧ ((x04 - x08) ≤ (t - 1)) ∧ ((x08 - x48) ≤ (t - 1))))) : ((x08 ≤ x48) ∨ ((x04 - x48) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x48) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause10083 (t x04 x08 x48 : ℝ) (h : (((x04 ≤ x08) ∧ (x08 ≤ x48) ∧ ((x48 - x04) ≥ 1) ∧ ((x08 - x04) ≤ (t - 1)) ∧ ((x48 - x08) ≤ (t - 1))) ∨ ((x48 ≤ x08) ∧ (x08 ≤ x04) ∧ ((x04 - x48) ≥ 1) ∧ ((x04 - x08) ≤ (t - 1)) ∧ ((x08 - x48) ≤ (t - 1))))) : ((x08 ≤ x48) ∨ ((x04 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause10084 (t x04 x08 x48 : ℝ) (h : (((x04 ≤ x08) ∧ (x08 ≤ x48) ∧ ((x48 - x04) ≥ 1) ∧ ((x08 - x04) ≤ (t - 1)) ∧ ((x48 - x08) ≤ (t - 1))) ∨ ((x48 ≤ x08) ∧ (x08 ≤ x04) ∧ ((x04 - x48) ≥ 1) ∧ ((x04 - x08) ≤ (t - 1)) ∧ ((x08 - x48) ≤ (t - 1))))) : ((x08 ≤ x48) ∨ ((x08 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause10085 (t x04 x08 x48 : ℝ) (h : (((x04 ≤ x08) ∧ (x08 ≤ x48) ∧ ((x48 - x04) ≥ 1) ∧ ((x08 - x04) ≤ (t - 1)) ∧ ((x48 - x08) ≤ (t - 1))) ∨ ((x48 ≤ x08) ∧ (x08 ≤ x04) ∧ ((x04 - x48) ≥ 1) ∧ ((x04 - x08) ≤ (t - 1)) ∧ ((x08 - x48) ≤ (t - 1))))) : (((x48 - x04) ≥ 1) ∨ (x48 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x04) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause10086 (t x04 x08 x48 : ℝ) (h : (((x04 ≤ x08) ∧ (x08 ≤ x48) ∧ ((x48 - x04) ≥ 1) ∧ ((x08 - x04) ≤ (t - 1)) ∧ ((x48 - x08) ≤ (t - 1))) ∨ ((x48 ≤ x08) ∧ (x08 ≤ x04) ∧ ((x04 - x48) ≥ 1) ∧ ((x04 - x08) ≤ (t - 1)) ∧ ((x08 - x48) ≤ (t - 1))))) : (((x48 - x04) ≥ 1) ∨ (x08 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x04) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause10087 (t x04 x08 x48 : ℝ) (h : (((x04 ≤ x08) ∧ (x08 ≤ x48) ∧ ((x48 - x04) ≥ 1) ∧ ((x08 - x04) ≤ (t - 1)) ∧ ((x48 - x08) ≤ (t - 1))) ∨ ((x48 ≤ x08) ∧ (x08 ≤ x04) ∧ ((x04 - x48) ≥ 1) ∧ ((x04 - x08) ≤ (t - 1)) ∧ ((x08 - x48) ≤ (t - 1))))) : (((x48 - x04) ≥ 1) ∨ ((x04 - x48) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x04) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x48) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause10088 (t x04 x08 x48 : ℝ) (h : (((x04 ≤ x08) ∧ (x08 ≤ x48) ∧ ((x48 - x04) ≥ 1) ∧ ((x08 - x04) ≤ (t - 1)) ∧ ((x48 - x08) ≤ (t - 1))) ∨ ((x48 ≤ x08) ∧ (x08 ≤ x04) ∧ ((x04 - x48) ≥ 1) ∧ ((x04 - x08) ≤ (t - 1)) ∧ ((x08 - x48) ≤ (t - 1))))) : (((x48 - x04) ≥ 1) ∨ ((x04 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x04) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause10089 (t x04 x08 x48 : ℝ) (h : (((x04 ≤ x08) ∧ (x08 ≤ x48) ∧ ((x48 - x04) ≥ 1) ∧ ((x08 - x04) ≤ (t - 1)) ∧ ((x48 - x08) ≤ (t - 1))) ∨ ((x48 ≤ x08) ∧ (x08 ≤ x04) ∧ ((x04 - x48) ≥ 1) ∧ ((x04 - x08) ≤ (t - 1)) ∧ ((x08 - x48) ≤ (t - 1))))) : (((x48 - x04) ≥ 1) ∨ ((x08 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x04) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause10090 (t x04 x08 x48 : ℝ) (h : (((x04 ≤ x08) ∧ (x08 ≤ x48) ∧ ((x48 - x04) ≥ 1) ∧ ((x08 - x04) ≤ (t - 1)) ∧ ((x48 - x08) ≤ (t - 1))) ∨ ((x48 ≤ x08) ∧ (x08 ≤ x04) ∧ ((x04 - x48) ≥ 1) ∧ ((x04 - x08) ≤ (t - 1)) ∧ ((x08 - x48) ≤ (t - 1))))) : (((x08 - x04) ≤ (t - 1)) ∨ (x48 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause10091 (t x04 x08 x48 : ℝ) (h : (((x04 ≤ x08) ∧ (x08 ≤ x48) ∧ ((x48 - x04) ≥ 1) ∧ ((x08 - x04) ≤ (t - 1)) ∧ ((x48 - x08) ≤ (t - 1))) ∨ ((x48 ≤ x08) ∧ (x08 ≤ x04) ∧ ((x04 - x48) ≥ 1) ∧ ((x04 - x08) ≤ (t - 1)) ∧ ((x08 - x48) ≤ (t - 1))))) : (((x08 - x04) ≤ (t - 1)) ∨ (x08 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause10092 (t x04 x08 x48 : ℝ) (h : (((x04 ≤ x08) ∧ (x08 ≤ x48) ∧ ((x48 - x04) ≥ 1) ∧ ((x08 - x04) ≤ (t - 1)) ∧ ((x48 - x08) ≤ (t - 1))) ∨ ((x48 ≤ x08) ∧ (x08 ≤ x04) ∧ ((x04 - x48) ≥ 1) ∧ ((x04 - x08) ≤ (t - 1)) ∧ ((x08 - x48) ≤ (t - 1))))) : (((x08 - x04) ≤ (t - 1)) ∨ ((x04 - x48) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x48) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause10093 (t x04 x08 x48 : ℝ) (h : (((x04 ≤ x08) ∧ (x08 ≤ x48) ∧ ((x48 - x04) ≥ 1) ∧ ((x08 - x04) ≤ (t - 1)) ∧ ((x48 - x08) ≤ (t - 1))) ∨ ((x48 ≤ x08) ∧ (x08 ≤ x04) ∧ ((x04 - x48) ≥ 1) ∧ ((x04 - x08) ≤ (t - 1)) ∧ ((x08 - x48) ≤ (t - 1))))) : (((x08 - x04) ≤ (t - 1)) ∨ ((x04 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause10094 (t x04 x08 x48 : ℝ) (h : (((x04 ≤ x08) ∧ (x08 ≤ x48) ∧ ((x48 - x04) ≥ 1) ∧ ((x08 - x04) ≤ (t - 1)) ∧ ((x48 - x08) ≤ (t - 1))) ∨ ((x48 ≤ x08) ∧ (x08 ≤ x04) ∧ ((x04 - x48) ≥ 1) ∧ ((x04 - x08) ≤ (t - 1)) ∧ ((x08 - x48) ≤ (t - 1))))) : (((x08 - x04) ≤ (t - 1)) ∨ ((x08 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause10095 (t x04 x08 x48 : ℝ) (h : (((x04 ≤ x08) ∧ (x08 ≤ x48) ∧ ((x48 - x04) ≥ 1) ∧ ((x08 - x04) ≤ (t - 1)) ∧ ((x48 - x08) ≤ (t - 1))) ∨ ((x48 ≤ x08) ∧ (x08 ≤ x04) ∧ ((x04 - x48) ≥ 1) ∧ ((x04 - x08) ≤ (t - 1)) ∧ ((x08 - x48) ≤ (t - 1))))) : (((x48 - x08) ≤ (t - 1)) ∨ (x48 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause10096 (t x04 x08 x48 : ℝ) (h : (((x04 ≤ x08) ∧ (x08 ≤ x48) ∧ ((x48 - x04) ≥ 1) ∧ ((x08 - x04) ≤ (t - 1)) ∧ ((x48 - x08) ≤ (t - 1))) ∨ ((x48 ≤ x08) ∧ (x08 ≤ x04) ∧ ((x04 - x48) ≥ 1) ∧ ((x04 - x08) ≤ (t - 1)) ∧ ((x08 - x48) ≤ (t - 1))))) : (((x48 - x08) ≤ (t - 1)) ∨ (x08 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause10097 (t x04 x08 x48 : ℝ) (h : (((x04 ≤ x08) ∧ (x08 ≤ x48) ∧ ((x48 - x04) ≥ 1) ∧ ((x08 - x04) ≤ (t - 1)) ∧ ((x48 - x08) ≤ (t - 1))) ∨ ((x48 ≤ x08) ∧ (x08 ≤ x04) ∧ ((x04 - x48) ≥ 1) ∧ ((x04 - x08) ≤ (t - 1)) ∧ ((x08 - x48) ≤ (t - 1))))) : (((x48 - x08) ≤ (t - 1)) ∨ ((x04 - x48) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x48) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause10098 (t x04 x08 x48 : ℝ) (h : (((x04 ≤ x08) ∧ (x08 ≤ x48) ∧ ((x48 - x04) ≥ 1) ∧ ((x08 - x04) ≤ (t - 1)) ∧ ((x48 - x08) ≤ (t - 1))) ∨ ((x48 ≤ x08) ∧ (x08 ≤ x04) ∧ ((x04 - x48) ≥ 1) ∧ ((x04 - x08) ≤ (t - 1)) ∧ ((x08 - x48) ≤ (t - 1))))) : (((x48 - x08) ≤ (t - 1)) ∨ ((x04 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause10099 (t x04 x08 x48 : ℝ) (h : (((x04 ≤ x08) ∧ (x08 ≤ x48) ∧ ((x48 - x04) ≥ 1) ∧ ((x08 - x04) ≤ (t - 1)) ∧ ((x48 - x08) ≤ (t - 1))) ∨ ((x48 ≤ x08) ∧ (x08 ≤ x04) ∧ ((x04 - x48) ≥ 1) ∧ ((x04 - x08) ≤ (t - 1)) ∧ ((x08 - x48) ≤ (t - 1))))) : (((x48 - x08) ≤ (t - 1)) ∨ ((x08 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause10100 (x06 x46 x67 : ℝ) : ((¬ ((x06 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x06 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1030 x06 x46 x67
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u1 u2))) h

theorem clause10101 (t x04 x06 x46 x48 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + ((-1) * x46) + x48) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x48)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x06)) ≤ 0) := by
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
  have u4 : ((t + ((-1) * x46) + x48) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1031 t x04 x06 x46 x48 x67
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u1 u3)))))) h

theorem clause10102 (x04 x14 x47 : ℝ) : ((¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1035 x04 x14 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause10103 (x02 x24 x26 : ℝ) : ((¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1036 x02 x24 x26
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 u0))) h

theorem clause10104 (x06 x26 x46 : ℝ) : (((x06 + ((-1) * x46)) ≥ 0) ∨ (¬ ((x26 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x26)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 + ((-1) * x46)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ((x26 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1037 x06 x26 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 u1)))) h

theorem clause10105 (x06 x16 x67 : ℝ) : ((¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x16)) ≥ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x06 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1038 x06 x16 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 u1)))) h

theorem clause10121 (t x24 x28 x48 : ℝ) : (((x24 + ((-1) * x48)) ≤ (-1)) ∨ ((x24 + ((-1) * x48)) ≥ 1) ∨ (¬ (x24 ≤ x28)) ∨ (¬ (x28 ≤ x48)) ∨ (¬ ((x48 - x24) ≥ 1)) ∨ (¬ ((x28 - x24) ≤ (t - 1))) ∨ (¬ ((x48 - x28) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x48)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x48)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x48 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x28 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1046 t x24 x28 x48
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause10146 (t x24 x28 x48 : ℝ) : (((x24 + ((-1) * x48)) ≤ (-1)) ∨ ((x24 + ((-1) * x48)) ≥ 1) ∨ (¬ (x48 ≤ x28)) ∨ (¬ (x28 ≤ x24)) ∨ (¬ ((x24 - x48) ≥ 1)) ∨ (¬ ((x24 - x28) ≤ (t - 1))) ∨ (¬ ((x28 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x48)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x48)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x48 ≤ x28) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x28 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x48) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x28) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x28 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1046 t x24 x28 x48
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause10209 (t x24 x28 x48 : ℝ) (h : (((x24 ≤ x28) ∧ (x28 ≤ x48) ∧ ((x48 - x24) ≥ 1) ∧ ((x28 - x24) ≤ (t - 1)) ∧ ((x48 - x28) ≤ (t - 1))) ∨ ((x48 ≤ x28) ∧ (x28 ≤ x24) ∧ ((x24 - x48) ≥ 1) ∧ ((x24 - x28) ≤ (t - 1)) ∧ ((x28 - x48) ≤ (t - 1))))) : ((x24 ≤ x28) ∨ (x48 ≤ x28)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x28) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause10210 (t x24 x28 x48 : ℝ) (h : (((x24 ≤ x28) ∧ (x28 ≤ x48) ∧ ((x48 - x24) ≥ 1) ∧ ((x28 - x24) ≤ (t - 1)) ∧ ((x48 - x28) ≤ (t - 1))) ∨ ((x48 ≤ x28) ∧ (x28 ≤ x24) ∧ ((x24 - x48) ≥ 1) ∧ ((x24 - x28) ≤ (t - 1)) ∧ ((x28 - x48) ≤ (t - 1))))) : ((x24 ≤ x28) ∨ (x28 ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x24) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause10211 (t x24 x28 x48 : ℝ) (h : (((x24 ≤ x28) ∧ (x28 ≤ x48) ∧ ((x48 - x24) ≥ 1) ∧ ((x28 - x24) ≤ (t - 1)) ∧ ((x48 - x28) ≤ (t - 1))) ∨ ((x48 ≤ x28) ∧ (x28 ≤ x24) ∧ ((x24 - x48) ≥ 1) ∧ ((x24 - x28) ≤ (t - 1)) ∧ ((x28 - x48) ≤ (t - 1))))) : ((x24 ≤ x28) ∨ ((x24 - x48) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x48) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause10212 (t x24 x28 x48 : ℝ) (h : (((x24 ≤ x28) ∧ (x28 ≤ x48) ∧ ((x48 - x24) ≥ 1) ∧ ((x28 - x24) ≤ (t - 1)) ∧ ((x48 - x28) ≤ (t - 1))) ∨ ((x48 ≤ x28) ∧ (x28 ≤ x24) ∧ ((x24 - x48) ≥ 1) ∧ ((x24 - x28) ≤ (t - 1)) ∧ ((x28 - x48) ≤ (t - 1))))) : ((x24 ≤ x28) ∨ ((x24 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause10213 (t x24 x28 x48 : ℝ) (h : (((x24 ≤ x28) ∧ (x28 ≤ x48) ∧ ((x48 - x24) ≥ 1) ∧ ((x28 - x24) ≤ (t - 1)) ∧ ((x48 - x28) ≤ (t - 1))) ∨ ((x48 ≤ x28) ∧ (x28 ≤ x24) ∧ ((x24 - x48) ≥ 1) ∧ ((x24 - x28) ≤ (t - 1)) ∧ ((x28 - x48) ≤ (t - 1))))) : ((x24 ≤ x28) ∨ ((x28 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≤ x28) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause10214 (t x24 x28 x48 : ℝ) (h : (((x24 ≤ x28) ∧ (x28 ≤ x48) ∧ ((x48 - x24) ≥ 1) ∧ ((x28 - x24) ≤ (t - 1)) ∧ ((x48 - x28) ≤ (t - 1))) ∨ ((x48 ≤ x28) ∧ (x28 ≤ x24) ∧ ((x24 - x48) ≥ 1) ∧ ((x24 - x28) ≤ (t - 1)) ∧ ((x28 - x48) ≤ (t - 1))))) : ((x28 ≤ x48) ∨ (x48 ≤ x28)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x28 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x28) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause10215 (t x24 x28 x48 : ℝ) (h : (((x24 ≤ x28) ∧ (x28 ≤ x48) ∧ ((x48 - x24) ≥ 1) ∧ ((x28 - x24) ≤ (t - 1)) ∧ ((x48 - x28) ≤ (t - 1))) ∨ ((x48 ≤ x28) ∧ (x28 ≤ x24) ∧ ((x24 - x48) ≥ 1) ∧ ((x24 - x28) ≤ (t - 1)) ∧ ((x28 - x48) ≤ (t - 1))))) : ((x28 ≤ x48) ∨ (x28 ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x28 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x24) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause10216 (t x24 x28 x48 : ℝ) (h : (((x24 ≤ x28) ∧ (x28 ≤ x48) ∧ ((x48 - x24) ≥ 1) ∧ ((x28 - x24) ≤ (t - 1)) ∧ ((x48 - x28) ≤ (t - 1))) ∨ ((x48 ≤ x28) ∧ (x28 ≤ x24) ∧ ((x24 - x48) ≥ 1) ∧ ((x24 - x28) ≤ (t - 1)) ∧ ((x28 - x48) ≤ (t - 1))))) : ((x28 ≤ x48) ∨ ((x24 - x48) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x28 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x48) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause10217 (t x24 x28 x48 : ℝ) (h : (((x24 ≤ x28) ∧ (x28 ≤ x48) ∧ ((x48 - x24) ≥ 1) ∧ ((x28 - x24) ≤ (t - 1)) ∧ ((x48 - x28) ≤ (t - 1))) ∨ ((x48 ≤ x28) ∧ (x28 ≤ x24) ∧ ((x24 - x48) ≥ 1) ∧ ((x24 - x28) ≤ (t - 1)) ∧ ((x28 - x48) ≤ (t - 1))))) : ((x28 ≤ x48) ∨ ((x24 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x28 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause10218 (t x24 x28 x48 : ℝ) (h : (((x24 ≤ x28) ∧ (x28 ≤ x48) ∧ ((x48 - x24) ≥ 1) ∧ ((x28 - x24) ≤ (t - 1)) ∧ ((x48 - x28) ≤ (t - 1))) ∨ ((x48 ≤ x28) ∧ (x28 ≤ x24) ∧ ((x24 - x48) ≥ 1) ∧ ((x24 - x28) ≤ (t - 1)) ∧ ((x28 - x48) ≤ (t - 1))))) : ((x28 ≤ x48) ∨ ((x28 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x28 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause10219 (t x24 x28 x48 : ℝ) (h : (((x24 ≤ x28) ∧ (x28 ≤ x48) ∧ ((x48 - x24) ≥ 1) ∧ ((x28 - x24) ≤ (t - 1)) ∧ ((x48 - x28) ≤ (t - 1))) ∨ ((x48 ≤ x28) ∧ (x28 ≤ x24) ∧ ((x24 - x48) ≥ 1) ∧ ((x24 - x28) ≤ (t - 1)) ∧ ((x28 - x48) ≤ (t - 1))))) : (((x48 - x24) ≥ 1) ∨ (x48 ≤ x28)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x24) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x28) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause10220 (t x24 x28 x48 : ℝ) (h : (((x24 ≤ x28) ∧ (x28 ≤ x48) ∧ ((x48 - x24) ≥ 1) ∧ ((x28 - x24) ≤ (t - 1)) ∧ ((x48 - x28) ≤ (t - 1))) ∨ ((x48 ≤ x28) ∧ (x28 ≤ x24) ∧ ((x24 - x48) ≥ 1) ∧ ((x24 - x28) ≤ (t - 1)) ∧ ((x28 - x48) ≤ (t - 1))))) : (((x48 - x24) ≥ 1) ∨ (x28 ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x24) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x24) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause10221 (t x24 x28 x48 : ℝ) (h : (((x24 ≤ x28) ∧ (x28 ≤ x48) ∧ ((x48 - x24) ≥ 1) ∧ ((x28 - x24) ≤ (t - 1)) ∧ ((x48 - x28) ≤ (t - 1))) ∨ ((x48 ≤ x28) ∧ (x28 ≤ x24) ∧ ((x24 - x48) ≥ 1) ∧ ((x24 - x28) ≤ (t - 1)) ∧ ((x28 - x48) ≤ (t - 1))))) : (((x48 - x24) ≥ 1) ∨ ((x24 - x48) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x24) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x48) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause10222 (t x24 x28 x48 : ℝ) (h : (((x24 ≤ x28) ∧ (x28 ≤ x48) ∧ ((x48 - x24) ≥ 1) ∧ ((x28 - x24) ≤ (t - 1)) ∧ ((x48 - x28) ≤ (t - 1))) ∨ ((x48 ≤ x28) ∧ (x28 ≤ x24) ∧ ((x24 - x48) ≥ 1) ∧ ((x24 - x28) ≤ (t - 1)) ∧ ((x28 - x48) ≤ (t - 1))))) : (((x48 - x24) ≥ 1) ∨ ((x24 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x24) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause10223 (t x24 x28 x48 : ℝ) (h : (((x24 ≤ x28) ∧ (x28 ≤ x48) ∧ ((x48 - x24) ≥ 1) ∧ ((x28 - x24) ≤ (t - 1)) ∧ ((x48 - x28) ≤ (t - 1))) ∨ ((x48 ≤ x28) ∧ (x28 ≤ x24) ∧ ((x24 - x48) ≥ 1) ∧ ((x24 - x28) ≤ (t - 1)) ∧ ((x28 - x48) ≤ (t - 1))))) : (((x48 - x24) ≥ 1) ∨ ((x28 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x24) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause10224 (t x24 x28 x48 : ℝ) (h : (((x24 ≤ x28) ∧ (x28 ≤ x48) ∧ ((x48 - x24) ≥ 1) ∧ ((x28 - x24) ≤ (t - 1)) ∧ ((x48 - x28) ≤ (t - 1))) ∨ ((x48 ≤ x28) ∧ (x28 ≤ x24) ∧ ((x24 - x48) ≥ 1) ∧ ((x24 - x28) ≤ (t - 1)) ∧ ((x28 - x48) ≤ (t - 1))))) : (((x28 - x24) ≤ (t - 1)) ∨ (x48 ≤ x28)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x24) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x28) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause10225 (t x24 x28 x48 : ℝ) (h : (((x24 ≤ x28) ∧ (x28 ≤ x48) ∧ ((x48 - x24) ≥ 1) ∧ ((x28 - x24) ≤ (t - 1)) ∧ ((x48 - x28) ≤ (t - 1))) ∨ ((x48 ≤ x28) ∧ (x28 ≤ x24) ∧ ((x24 - x48) ≥ 1) ∧ ((x24 - x28) ≤ (t - 1)) ∧ ((x28 - x48) ≤ (t - 1))))) : (((x28 - x24) ≤ (t - 1)) ∨ (x28 ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x24) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x24) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause10226 (t x24 x28 x48 : ℝ) (h : (((x24 ≤ x28) ∧ (x28 ≤ x48) ∧ ((x48 - x24) ≥ 1) ∧ ((x28 - x24) ≤ (t - 1)) ∧ ((x48 - x28) ≤ (t - 1))) ∨ ((x48 ≤ x28) ∧ (x28 ≤ x24) ∧ ((x24 - x48) ≥ 1) ∧ ((x24 - x28) ≤ (t - 1)) ∧ ((x28 - x48) ≤ (t - 1))))) : (((x28 - x24) ≤ (t - 1)) ∨ ((x24 - x48) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x24) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x48) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause10227 (t x24 x28 x48 : ℝ) (h : (((x24 ≤ x28) ∧ (x28 ≤ x48) ∧ ((x48 - x24) ≥ 1) ∧ ((x28 - x24) ≤ (t - 1)) ∧ ((x48 - x28) ≤ (t - 1))) ∨ ((x48 ≤ x28) ∧ (x28 ≤ x24) ∧ ((x24 - x48) ≥ 1) ∧ ((x24 - x28) ≤ (t - 1)) ∧ ((x28 - x48) ≤ (t - 1))))) : (((x28 - x24) ≤ (t - 1)) ∨ ((x24 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x24) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause10228 (t x24 x28 x48 : ℝ) (h : (((x24 ≤ x28) ∧ (x28 ≤ x48) ∧ ((x48 - x24) ≥ 1) ∧ ((x28 - x24) ≤ (t - 1)) ∧ ((x48 - x28) ≤ (t - 1))) ∨ ((x48 ≤ x28) ∧ (x28 ≤ x24) ∧ ((x24 - x48) ≥ 1) ∧ ((x24 - x28) ≤ (t - 1)) ∧ ((x28 - x48) ≤ (t - 1))))) : (((x28 - x24) ≤ (t - 1)) ∨ ((x28 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x28 - x24) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause10229 (t x24 x28 x48 : ℝ) (h : (((x24 ≤ x28) ∧ (x28 ≤ x48) ∧ ((x48 - x24) ≥ 1) ∧ ((x28 - x24) ≤ (t - 1)) ∧ ((x48 - x28) ≤ (t - 1))) ∨ ((x48 ≤ x28) ∧ (x28 ≤ x24) ∧ ((x24 - x48) ≥ 1) ∧ ((x24 - x28) ≤ (t - 1)) ∧ ((x28 - x48) ≤ (t - 1))))) : (((x48 - x28) ≤ (t - 1)) ∨ (x48 ≤ x28)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x28) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x28) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause10230 (t x24 x28 x48 : ℝ) (h : (((x24 ≤ x28) ∧ (x28 ≤ x48) ∧ ((x48 - x24) ≥ 1) ∧ ((x28 - x24) ≤ (t - 1)) ∧ ((x48 - x28) ≤ (t - 1))) ∨ ((x48 ≤ x28) ∧ (x28 ≤ x24) ∧ ((x24 - x48) ≥ 1) ∧ ((x24 - x28) ≤ (t - 1)) ∧ ((x28 - x48) ≤ (t - 1))))) : (((x48 - x28) ≤ (t - 1)) ∨ (x28 ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x28) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x28 ≤ x24) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause10231 (t x24 x28 x48 : ℝ) (h : (((x24 ≤ x28) ∧ (x28 ≤ x48) ∧ ((x48 - x24) ≥ 1) ∧ ((x28 - x24) ≤ (t - 1)) ∧ ((x48 - x28) ≤ (t - 1))) ∨ ((x48 ≤ x28) ∧ (x28 ≤ x24) ∧ ((x24 - x48) ≥ 1) ∧ ((x24 - x28) ≤ (t - 1)) ∧ ((x28 - x48) ≤ (t - 1))))) : (((x48 - x28) ≤ (t - 1)) ∨ ((x24 - x48) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x28) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x48) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause10232 (t x24 x28 x48 : ℝ) (h : (((x24 ≤ x28) ∧ (x28 ≤ x48) ∧ ((x48 - x24) ≥ 1) ∧ ((x28 - x24) ≤ (t - 1)) ∧ ((x48 - x28) ≤ (t - 1))) ∨ ((x48 ≤ x28) ∧ (x28 ≤ x24) ∧ ((x24 - x48) ≥ 1) ∧ ((x24 - x28) ≤ (t - 1)) ∧ ((x28 - x48) ≤ (t - 1))))) : (((x48 - x28) ≤ (t - 1)) ∨ ((x24 - x28) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x28) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x28) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause10233 (t x24 x28 x48 : ℝ) (h : (((x24 ≤ x28) ∧ (x28 ≤ x48) ∧ ((x48 - x24) ≥ 1) ∧ ((x28 - x24) ≤ (t - 1)) ∧ ((x48 - x28) ≤ (t - 1))) ∨ ((x48 ≤ x28) ∧ (x28 ≤ x24) ∧ ((x24 - x48) ≥ 1) ∧ ((x24 - x28) ≤ (t - 1)) ∧ ((x28 - x48) ≤ (t - 1))))) : (((x48 - x28) ≤ (t - 1)) ∨ ((x28 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x28) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x28 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause10234 (t x01 x16 x17 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + x16 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x67)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x16 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1048 t x01 x16 x17 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u5 u4))))))) h

theorem clause10236 (t x02 x24 x45 x56 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ (x68 ≥ 0)) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0)) := by
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
  have u4 : (x68 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1050 t x02 x24 x45 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u5 (And.intro u6 (And.intro u2 (And.intro u0 u4)))))))) h

theorem clause10237 (t x25 x27 x56 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x27)) ≤ 0)) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x56 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 + ((-1) * x27)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1054 t x25 x27 x56 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u4 (And.intro u3 u5))))))) h

theorem clause10238 (t x05 x07 x25 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x07)) ≥ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((t + ((-1) * x05) + x25) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1)))) := by
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
  have u3 : ((t + ((-1) * x05) + x25) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1055 t x05 x07 x25 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u0 (And.intro u4 (And.intro u1 u3))))))) h

theorem clause10239 (t x02 x03 x24 x36 x48 x67 x78 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x03) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + x48 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x48)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x02) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th1057 t x02 x03 x24 x36 x48 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u7 (And.intro u3 (And.intro u6 (And.intro u4 (And.intro u0 u5))))))))) h

theorem clause10241 (t x01 x15 x17 x35 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + x15 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x57)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x15 + ((-1) * x35)) ≥ 1) := by
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
  have h := NineTheoryTrial.th1060 t x01 x15 x17 x35 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u4 (And.intro u3 (And.intro u1 u5))))))) h

theorem clause10242 (t x01 x15 x16 x56 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x56) + x58) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x58)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x56) + x58) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x16 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1061 t x01 x15 x16 x56 x58
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u3 (And.intro u4 (And.intro u2 (And.intro u0 u1)))))) h

theorem clause10243 (t x01 x16 x17 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + x16 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x67)) ≤ 0))) := by
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
  have u3 : ((t + x16 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1063 t x01 x16 x17 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u0 (And.intro u2 (And.intro u5 u1))))))) h

theorem clause10244 (x16 : ℝ) (h : (x16 ≥ 0)) : ((x16 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause10245 (x05 x15 x56 : ℝ) : ((¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x15)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1067 x05 x15 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 u0)))) h

theorem clause10246 (t x01 x14 x15 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x45 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
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
  have h := NineTheoryTrial.th1068 t x01 x14 x15 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u5 u4))))))) h

theorem clause10247 (t x01 x04 x12 x13 x14 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1))) := by
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
  have u3 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
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
  have u6 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1069 t x01 x04 x12 x13 x14 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u5 (And.intro u3 u4)))))))) h

theorem clause10248 (x01 x14 x17 : ℝ) : ((¬ ((x14 + ((-1) * x17)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x14 + ((-1) * x17)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1071 x01 x14 x17
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause10249 (t x01 x13 x17 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
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
  have u4 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1077 t x01 x13 x17 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u6 (And.intro u1 (And.intro u3 u5)))))))) h

theorem clause10250 (x01 x16 x17 : ℝ) : ((¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ ((x01 + ((-1) * x17)) ≤ (-1)) ∨ (¬ ((x16 + ((-1) * x17)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x17)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x16 + ((-1) * x17)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1078 x01 x16 x17
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause10251 (t x06 x45 x56 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x67)) ≥ 0)) ∨ (¬ ((t + x06 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x57 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x06 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1079 t x06 x45 x56 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u5 u1))))))) h

theorem clause10252 (x45 x56 x57 : ℝ) : ((¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x57)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1080 x45 x56 x57
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u0 u2))) h

theorem clause10253 (t x01 x12 x13 x16 x17 x36 x47 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((t + x47 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x17)) ≥ 0))) := by
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
  have u6 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x16 + ((-1) * x36)) ≤ 0) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th1083 t x01 x12 x13 x16 x17 x36 x47 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u9 (And.intro u1 (And.intro u2 (And.intro u6 (And.intro u8 (And.intro u7 (And.intro u4 u5))))))))))) h

theorem clause10254 (x46 x56 x67 : ℝ) : ((¬ ((x46 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1))) := by
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
  have u2 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1084 x46 x56 x67
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 u0))) h

theorem clause10255 (x17 x47 x78 : ℝ) : ((¬ ((x17 + ((-1) * x47)) ≤ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x17 + ((-1) * x47)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1086 x17 x47 x78
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u1 u2))) h

theorem clause10256 (t x01 x13 x16 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
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
  have u3 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1087 t x01 x13 x16 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u3 (And.intro u1 (And.intro u6 u4)))))))) h

theorem clause10257 (t x01 x07 x15 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x07 + ((-1) * x67)) ≥ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ ((t + x01 + ((-1) * x07)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x07 + ((-1) * x67)) ≥ 0) := by
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
  have u5 : ((t + x01 + ((-1) * x07)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1088 t x01 x07 x15 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u3 u4))))))) h

theorem clause10258 (t x01 x07 x17 : ℝ) : ((¬ (x17 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ ((t + x01 + ((-1) * x07)) ≥ 1) ∨ ((t + ((-1) * x07)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (x17 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + x01 + ((-1) * x07)) ≥ 1) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x07)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th1089 t x01 x07 x17
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u2 u0))))) h

theorem clause10259 (x15 x25 x56 : ℝ) : ((¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x25)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x15 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1094 x15 x25 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause10260 (x47 : ℝ) (h : (x47 ≥ 0)) : ((x47 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x47 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause10261 (t x01 x04 x12 x13 x14 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1))) := by
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
  have u3 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
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
  have u6 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1096 t x01 x04 x12 x13 x14 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u4 (And.intro u2 (And.intro u5 u6)))))))) h

theorem clause10262 (t x01 x13 x14 x34 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1097 t x01 x13 x14 x34 x45
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u5 (And.intro u1 (And.intro u2 (And.intro u4 (And.intro u0 u3))))))) h

theorem clause10263 (t x01 x14 x15 x34 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x14 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x14 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x45)) ≥ 1) := by
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
  have u5 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1098 t x01 x14 x15 x34 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u3 u5))))))) h

theorem clause10265 (x34 x45 x47 : ℝ) : ((¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ ((x34 + ((-1) * x47)) ≥ 1) ∨ (¬ ((x45 + ((-1) * x47)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1104 x34 x45 x47
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause10266 (x05 x45 x57 : ℝ) : ((¬ ((x05 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x05 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1105 x05 x45 x57
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 u0))) h

theorem clause10267 (t x04 x24 x45 x46 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x24 ≥ 0)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ ((t + ((-1) * x57)) ≤ 0)) := by
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
  have u3 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1108 t x04 x24 x45 x46 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u6 (And.intro u3 (And.intro u0 (And.intro u4 u2)))))))) h

theorem clause10268 (t x14 x45 x46 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x46 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x46 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th1109 t x14 x45 x46 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u4 (And.intro u3 (And.intro u1 u2))))))) h

theorem clause10269 (x14 x45 x46 : ℝ) : ((¬ ((x45 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x45 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1110 x14 x45 x46
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u2 u1))) h

theorem clause10270 (x05 x45 x57 : ℝ) : ((¬ ((x05 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ ((x45 + ((-1) * x57)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x05 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x45 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1111 x05 x45 x57
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause10271 (t x01 x04 x12 x14 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x14) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th1114 t x01 x04 x12 x14 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u4 (And.intro u5 (And.intro u0 (And.intro u1 u3))))))) h

theorem clause10272 (t x01 x15 x16 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x15 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x56 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1116 t x01 x15 x16 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u6 (And.intro u2 (And.intro u5 (And.intro u3 (And.intro u1 u4)))))))) h

theorem clause10274 (t x01 x03 x12 x13 x14 x34 x45 x46 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x45) + x46) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1))) := by
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
  have u5 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x45) + x46) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th1118 t x01 x03 x12 x13 x14 x34 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u7 (And.intro u1 (And.intro u3 (And.intro u8 (And.intro u2 (And.intro u5 (And.intro u0 u6)))))))))) h

theorem clause10275 (t x01 x15 x16 x25 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((t + ((-1) * x15) + x25) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x16 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x15) + x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1119 t x01 x15 x16 x25 x56
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u1 u5)))))) h

theorem clause10276 (t x01 x16 x17 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((t + x16 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x67)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x16 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1120 t x01 x16 x17 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u5 u1))))))) h

theorem clause10277 (t x02 x03 x25 x34 x46 x57 x67 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x02) + x03) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
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
  have u4 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1121 t x02 x03 x25 x34 x46 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u3 (And.intro u4 (And.intro u0 (And.intro u7 (And.intro u6 u5))))))))) h

theorem clause10279 (t x02 x04 x25 x34 x46 x47 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x47) + x57) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((t + ((-1) * x02) + x04) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x47) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x02) + x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1124 t x02 x04 x25 x34 x46 x47 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u2 (And.intro u7 (And.intro u3 (And.intro u1 (And.intro u5 u6))))))))) h

theorem clause10280 (t x04 x24 x45 x46 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x45) + x46) ≥ 1))) := by
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
  have u4 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x45) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1125 t x04 x24 x45 x46 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u1 u2))))))) h

theorem clause10281 (t x14 x15 x45 x47 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x15)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x45) + x47) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x45) + x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1130 t x14 x15 x45 x47 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u4 (And.intro u2 u3))))))) h

theorem clause10282 (x15 x56 : ℝ) : ((¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th1133 x15 x56
  exact (fun hh => (Or.elim hh (fun hh => hh u0) (fun zz => ((fun hh => hh u1) zz)))) h

theorem clause10283 (x01 x14 x16 : ℝ) : (((x01 + ((-1) * x14)) ≤ (-1)) ∨ (¬ ((x14 + ((-1) * x16)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x14)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1137 x01 x14 x16
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause10284 (t x02 x24 x34 x45 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1140 t x02 x24 x34 x45 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u5 u2)))))))) h

theorem clause10285 (t x01 x04 x12 x14 x16 x45 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x14) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
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
  have u3 : ((x04 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x12) + x14) ≥ 1) := by
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
  have u7 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x16 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th1141 t x01 x04 x12 x14 x16 x45 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u8 (And.intro u4 (And.intro u2 (And.intro u0 (And.intro u7 (And.intro u5 (And.intro u1 u6)))))))))) h

theorem clause10287 (t x01 x13 x16 x17 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x17)) ≤ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
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
  have u4 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 + ((-1) * x17)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1144 t x01 x13 x16 x17 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u3 (And.intro u4 u6))))))))) h

theorem clause10288 (x47 x57 x67 : ℝ) : (((x47 + ((-1) * x67)) ≤ 0) ∨ (¬ ((x57 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((x47 + ((-1) * x57)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ((x57 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x47 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1145 x47 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 u0)))) h

theorem clause10289 (x45 x46 x47 x67 : ℝ) : ((¬ ((x45 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x47 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x47)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x45 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x47 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x47)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th1146 x45 x46 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u0 u1))))) h

theorem clause10291 (t x02 x24 x25 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1)) ∨ (¬ (x57 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x56)) ≥ 1) := by
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
  have h := NineTheoryTrial.th1152 t x02 x24 x25 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u1 (And.intro u6 (And.intro u5 u3))))))))) h

theorem clause10292 (x25 x45 x56 : ℝ) : ((¬ ((x25 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x25 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1153 x25 x45 x56
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u1 u2))) h

theorem clause10293 (t x02 x03 x12 x13 x25 x34 x48 x57 x78 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ ((x02 + ((-1) * x12)) ≥ 0) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + ((-1) * x48) + x78) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x48)) ≤ (-1)))) := by
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
  have u4 : ¬ ((x02 + ((-1) * x12)) ≥ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x25)) ≥ 1) := by
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
  have u8 : ((t + ((-1) * x48) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x34 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th1156 t x02 x03 x12 x13 x25 x34 x48 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u6 (And.intro u2 (And.intro u5 (And.intro u3 (And.intro u1 (And.intro u7 (And.intro u8 (And.intro u9 u0))))))))))) h

theorem clause10294 (t x25 x36 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1)) ∨ (¬ (x25 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
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
  have u5 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x25 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1158 t x25 x36 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u6 (And.intro u2 (And.intro u5 u4)))))))) h

theorem clause10295 (t x01 x14 x15 x45 x48 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((t + ((-1) * x45) + x48) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x48)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x15 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x45) + x48) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1166 t x01 x14 x15 x45 x48
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u5 u1))))))) h

theorem clause10296 (t x01 x13 x14 x15 x35 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x14)) ≤ 0)) ∨ (¬ (x13 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x58)) ≥ 1)) ∨ ((t + ((-1) * x35)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x58)) ≤ (-1)))) := by
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
  have u3 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x15 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1167 t x01 x13 x14 x15 x35 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u6 (And.intro u7 (And.intro u5 u4))))))))) h

theorem clause10297 (t x03 x12 x13 x25 x34 x47 x58 x78 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + x58 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1)))) := by
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
  have u4 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x58 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th1169 t x03 x12 x13 x25 x34 x47 x58 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u6 (And.intro u8 (And.intro u0 (And.intro u4 (And.intro u7 (And.intro u3 u5)))))))))) h

theorem clause10298 (t x26 x46 x47 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x46 + ((-1) * x47)) ≥ 0)) ∨ (¬ ((t + x26 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x46 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x26 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1170 t x26 x46 x47 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u1 (And.intro u3 (And.intro u0 u4))))))) h

theorem clause10299 (t x06 x26 x27 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + ((-1) * x06) + x26) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x27)) ≤ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x27 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x06) + x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x26 + ((-1) * x27)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1171 t x06 x26 x27 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u1 (And.intro u4 (And.intro u5 u3))))))) h

theorem clause10313 (t x01 x08 x18 : ℝ) : (((x01 + ((-1) * x18)) ≤ (-1)) ∨ ((x01 + ((-1) * x18)) ≥ 1) ∨ (¬ (x01 ≤ x08)) ∨ (¬ (x08 ≤ x18)) ∨ (¬ ((x18 - x01) ≥ 1)) ∨ (¬ ((x08 - x01) ≤ (t - 1))) ∨ (¬ ((x18 - x08) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x18)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x18)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x08) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x08 ≤ x18) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x18 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x08 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x18 - x08) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1175 t x01 x08 x18
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause10338 (t x01 x08 x18 : ℝ) : (((x01 + ((-1) * x18)) ≤ (-1)) ∨ ((x01 + ((-1) * x18)) ≥ 1) ∨ (¬ (x18 ≤ x08)) ∨ (¬ (x08 ≤ x01)) ∨ (¬ ((x01 - x18) ≥ 1)) ∨ (¬ ((x01 - x08) ≤ (t - 1))) ∨ (¬ ((x08 - x18) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x18)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x18)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x18 ≤ x08) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x08 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x18) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x08) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x08 - x18) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1175 t x01 x08 x18
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause10401 (t x01 x08 x18 : ℝ) (h : (((x01 ≤ x08) ∧ (x08 ≤ x18) ∧ ((x18 - x01) ≥ 1) ∧ ((x08 - x01) ≤ (t - 1)) ∧ ((x18 - x08) ≤ (t - 1))) ∨ ((x18 ≤ x08) ∧ (x08 ≤ x01) ∧ ((x01 - x18) ≥ 1) ∧ ((x01 - x08) ≤ (t - 1)) ∧ ((x08 - x18) ≤ (t - 1))))) : ((x01 ≤ x08) ∨ (x18 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause10402 (t x01 x08 x18 : ℝ) (h : (((x01 ≤ x08) ∧ (x08 ≤ x18) ∧ ((x18 - x01) ≥ 1) ∧ ((x08 - x01) ≤ (t - 1)) ∧ ((x18 - x08) ≤ (t - 1))) ∨ ((x18 ≤ x08) ∧ (x08 ≤ x01) ∧ ((x01 - x18) ≥ 1) ∧ ((x01 - x08) ≤ (t - 1)) ∧ ((x08 - x18) ≤ (t - 1))))) : ((x01 ≤ x08) ∨ (x08 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause10403 (t x01 x08 x18 : ℝ) (h : (((x01 ≤ x08) ∧ (x08 ≤ x18) ∧ ((x18 - x01) ≥ 1) ∧ ((x08 - x01) ≤ (t - 1)) ∧ ((x18 - x08) ≤ (t - 1))) ∨ ((x18 ≤ x08) ∧ (x08 ≤ x01) ∧ ((x01 - x18) ≥ 1) ∧ ((x01 - x08) ≤ (t - 1)) ∧ ((x08 - x18) ≤ (t - 1))))) : ((x01 ≤ x08) ∨ ((x01 - x18) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x18) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause10404 (t x01 x08 x18 : ℝ) (h : (((x01 ≤ x08) ∧ (x08 ≤ x18) ∧ ((x18 - x01) ≥ 1) ∧ ((x08 - x01) ≤ (t - 1)) ∧ ((x18 - x08) ≤ (t - 1))) ∨ ((x18 ≤ x08) ∧ (x08 ≤ x01) ∧ ((x01 - x18) ≥ 1) ∧ ((x01 - x08) ≤ (t - 1)) ∧ ((x08 - x18) ≤ (t - 1))))) : ((x01 ≤ x08) ∨ ((x01 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause10405 (t x01 x08 x18 : ℝ) (h : (((x01 ≤ x08) ∧ (x08 ≤ x18) ∧ ((x18 - x01) ≥ 1) ∧ ((x08 - x01) ≤ (t - 1)) ∧ ((x18 - x08) ≤ (t - 1))) ∨ ((x18 ≤ x08) ∧ (x08 ≤ x01) ∧ ((x01 - x18) ≥ 1) ∧ ((x01 - x08) ≤ (t - 1)) ∧ ((x08 - x18) ≤ (t - 1))))) : ((x01 ≤ x08) ∨ ((x08 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause10406 (t x01 x08 x18 : ℝ) (h : (((x01 ≤ x08) ∧ (x08 ≤ x18) ∧ ((x18 - x01) ≥ 1) ∧ ((x08 - x01) ≤ (t - 1)) ∧ ((x18 - x08) ≤ (t - 1))) ∨ ((x18 ≤ x08) ∧ (x08 ≤ x01) ∧ ((x01 - x18) ≥ 1) ∧ ((x01 - x08) ≤ (t - 1)) ∧ ((x08 - x18) ≤ (t - 1))))) : ((x08 ≤ x18) ∨ (x18 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause10407 (t x01 x08 x18 : ℝ) (h : (((x01 ≤ x08) ∧ (x08 ≤ x18) ∧ ((x18 - x01) ≥ 1) ∧ ((x08 - x01) ≤ (t - 1)) ∧ ((x18 - x08) ≤ (t - 1))) ∨ ((x18 ≤ x08) ∧ (x08 ≤ x01) ∧ ((x01 - x18) ≥ 1) ∧ ((x01 - x08) ≤ (t - 1)) ∧ ((x08 - x18) ≤ (t - 1))))) : ((x08 ≤ x18) ∨ (x08 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause10408 (t x01 x08 x18 : ℝ) (h : (((x01 ≤ x08) ∧ (x08 ≤ x18) ∧ ((x18 - x01) ≥ 1) ∧ ((x08 - x01) ≤ (t - 1)) ∧ ((x18 - x08) ≤ (t - 1))) ∨ ((x18 ≤ x08) ∧ (x08 ≤ x01) ∧ ((x01 - x18) ≥ 1) ∧ ((x01 - x08) ≤ (t - 1)) ∧ ((x08 - x18) ≤ (t - 1))))) : ((x08 ≤ x18) ∨ ((x01 - x18) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x18) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause10409 (t x01 x08 x18 : ℝ) (h : (((x01 ≤ x08) ∧ (x08 ≤ x18) ∧ ((x18 - x01) ≥ 1) ∧ ((x08 - x01) ≤ (t - 1)) ∧ ((x18 - x08) ≤ (t - 1))) ∨ ((x18 ≤ x08) ∧ (x08 ≤ x01) ∧ ((x01 - x18) ≥ 1) ∧ ((x01 - x08) ≤ (t - 1)) ∧ ((x08 - x18) ≤ (t - 1))))) : ((x08 ≤ x18) ∨ ((x01 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause10410 (t x01 x08 x18 : ℝ) (h : (((x01 ≤ x08) ∧ (x08 ≤ x18) ∧ ((x18 - x01) ≥ 1) ∧ ((x08 - x01) ≤ (t - 1)) ∧ ((x18 - x08) ≤ (t - 1))) ∨ ((x18 ≤ x08) ∧ (x08 ≤ x01) ∧ ((x01 - x18) ≥ 1) ∧ ((x01 - x08) ≤ (t - 1)) ∧ ((x08 - x18) ≤ (t - 1))))) : ((x08 ≤ x18) ∨ ((x08 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x18) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause10411 (t x01 x08 x18 : ℝ) (h : (((x01 ≤ x08) ∧ (x08 ≤ x18) ∧ ((x18 - x01) ≥ 1) ∧ ((x08 - x01) ≤ (t - 1)) ∧ ((x18 - x08) ≤ (t - 1))) ∨ ((x18 ≤ x08) ∧ (x08 ≤ x01) ∧ ((x01 - x18) ≥ 1) ∧ ((x01 - x08) ≤ (t - 1)) ∧ ((x08 - x18) ≤ (t - 1))))) : (((x18 - x01) ≥ 1) ∨ (x18 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause10412 (t x01 x08 x18 : ℝ) (h : (((x01 ≤ x08) ∧ (x08 ≤ x18) ∧ ((x18 - x01) ≥ 1) ∧ ((x08 - x01) ≤ (t - 1)) ∧ ((x18 - x08) ≤ (t - 1))) ∨ ((x18 ≤ x08) ∧ (x08 ≤ x01) ∧ ((x01 - x18) ≥ 1) ∧ ((x01 - x08) ≤ (t - 1)) ∧ ((x08 - x18) ≤ (t - 1))))) : (((x18 - x01) ≥ 1) ∨ (x08 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause10413 (t x01 x08 x18 : ℝ) (h : (((x01 ≤ x08) ∧ (x08 ≤ x18) ∧ ((x18 - x01) ≥ 1) ∧ ((x08 - x01) ≤ (t - 1)) ∧ ((x18 - x08) ≤ (t - 1))) ∨ ((x18 ≤ x08) ∧ (x08 ≤ x01) ∧ ((x01 - x18) ≥ 1) ∧ ((x01 - x08) ≤ (t - 1)) ∧ ((x08 - x18) ≤ (t - 1))))) : (((x18 - x01) ≥ 1) ∨ ((x01 - x18) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x18) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause10414 (t x01 x08 x18 : ℝ) (h : (((x01 ≤ x08) ∧ (x08 ≤ x18) ∧ ((x18 - x01) ≥ 1) ∧ ((x08 - x01) ≤ (t - 1)) ∧ ((x18 - x08) ≤ (t - 1))) ∨ ((x18 ≤ x08) ∧ (x08 ≤ x01) ∧ ((x01 - x18) ≥ 1) ∧ ((x01 - x08) ≤ (t - 1)) ∧ ((x08 - x18) ≤ (t - 1))))) : (((x18 - x01) ≥ 1) ∨ ((x01 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause10415 (t x01 x08 x18 : ℝ) (h : (((x01 ≤ x08) ∧ (x08 ≤ x18) ∧ ((x18 - x01) ≥ 1) ∧ ((x08 - x01) ≤ (t - 1)) ∧ ((x18 - x08) ≤ (t - 1))) ∨ ((x18 ≤ x08) ∧ (x08 ≤ x01) ∧ ((x01 - x18) ≥ 1) ∧ ((x01 - x08) ≤ (t - 1)) ∧ ((x08 - x18) ≤ (t - 1))))) : (((x18 - x01) ≥ 1) ∨ ((x08 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause10416 (t x01 x08 x18 : ℝ) (h : (((x01 ≤ x08) ∧ (x08 ≤ x18) ∧ ((x18 - x01) ≥ 1) ∧ ((x08 - x01) ≤ (t - 1)) ∧ ((x18 - x08) ≤ (t - 1))) ∨ ((x18 ≤ x08) ∧ (x08 ≤ x01) ∧ ((x01 - x18) ≥ 1) ∧ ((x01 - x08) ≤ (t - 1)) ∧ ((x08 - x18) ≤ (t - 1))))) : (((x08 - x01) ≤ (t - 1)) ∨ (x18 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause10417 (t x01 x08 x18 : ℝ) (h : (((x01 ≤ x08) ∧ (x08 ≤ x18) ∧ ((x18 - x01) ≥ 1) ∧ ((x08 - x01) ≤ (t - 1)) ∧ ((x18 - x08) ≤ (t - 1))) ∨ ((x18 ≤ x08) ∧ (x08 ≤ x01) ∧ ((x01 - x18) ≥ 1) ∧ ((x01 - x08) ≤ (t - 1)) ∧ ((x08 - x18) ≤ (t - 1))))) : (((x08 - x01) ≤ (t - 1)) ∨ (x08 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause10418 (t x01 x08 x18 : ℝ) (h : (((x01 ≤ x08) ∧ (x08 ≤ x18) ∧ ((x18 - x01) ≥ 1) ∧ ((x08 - x01) ≤ (t - 1)) ∧ ((x18 - x08) ≤ (t - 1))) ∨ ((x18 ≤ x08) ∧ (x08 ≤ x01) ∧ ((x01 - x18) ≥ 1) ∧ ((x01 - x08) ≤ (t - 1)) ∧ ((x08 - x18) ≤ (t - 1))))) : (((x08 - x01) ≤ (t - 1)) ∨ ((x01 - x18) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x18) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause10419 (t x01 x08 x18 : ℝ) (h : (((x01 ≤ x08) ∧ (x08 ≤ x18) ∧ ((x18 - x01) ≥ 1) ∧ ((x08 - x01) ≤ (t - 1)) ∧ ((x18 - x08) ≤ (t - 1))) ∨ ((x18 ≤ x08) ∧ (x08 ≤ x01) ∧ ((x01 - x18) ≥ 1) ∧ ((x01 - x08) ≤ (t - 1)) ∧ ((x08 - x18) ≤ (t - 1))))) : (((x08 - x01) ≤ (t - 1)) ∨ ((x01 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause10420 (t x01 x08 x18 : ℝ) (h : (((x01 ≤ x08) ∧ (x08 ≤ x18) ∧ ((x18 - x01) ≥ 1) ∧ ((x08 - x01) ≤ (t - 1)) ∧ ((x18 - x08) ≤ (t - 1))) ∨ ((x18 ≤ x08) ∧ (x08 ≤ x01) ∧ ((x01 - x18) ≥ 1) ∧ ((x01 - x08) ≤ (t - 1)) ∧ ((x08 - x18) ≤ (t - 1))))) : (((x08 - x01) ≤ (t - 1)) ∨ ((x08 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause10421 (t x01 x08 x18 : ℝ) (h : (((x01 ≤ x08) ∧ (x08 ≤ x18) ∧ ((x18 - x01) ≥ 1) ∧ ((x08 - x01) ≤ (t - 1)) ∧ ((x18 - x08) ≤ (t - 1))) ∨ ((x18 ≤ x08) ∧ (x08 ≤ x01) ∧ ((x01 - x18) ≥ 1) ∧ ((x01 - x08) ≤ (t - 1)) ∧ ((x08 - x18) ≤ (t - 1))))) : (((x18 - x08) ≤ (t - 1)) ∨ (x18 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x18 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause10422 (t x01 x08 x18 : ℝ) (h : (((x01 ≤ x08) ∧ (x08 ≤ x18) ∧ ((x18 - x01) ≥ 1) ∧ ((x08 - x01) ≤ (t - 1)) ∧ ((x18 - x08) ≤ (t - 1))) ∨ ((x18 ≤ x08) ∧ (x08 ≤ x01) ∧ ((x01 - x18) ≥ 1) ∧ ((x01 - x08) ≤ (t - 1)) ∧ ((x08 - x18) ≤ (t - 1))))) : (((x18 - x08) ≤ (t - 1)) ∨ (x08 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause10423 (t x01 x08 x18 : ℝ) (h : (((x01 ≤ x08) ∧ (x08 ≤ x18) ∧ ((x18 - x01) ≥ 1) ∧ ((x08 - x01) ≤ (t - 1)) ∧ ((x18 - x08) ≤ (t - 1))) ∨ ((x18 ≤ x08) ∧ (x08 ≤ x01) ∧ ((x01 - x18) ≥ 1) ∧ ((x01 - x08) ≤ (t - 1)) ∧ ((x08 - x18) ≤ (t - 1))))) : (((x18 - x08) ≤ (t - 1)) ∨ ((x01 - x18) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x18) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause10424 (t x01 x08 x18 : ℝ) (h : (((x01 ≤ x08) ∧ (x08 ≤ x18) ∧ ((x18 - x01) ≥ 1) ∧ ((x08 - x01) ≤ (t - 1)) ∧ ((x18 - x08) ≤ (t - 1))) ∨ ((x18 ≤ x08) ∧ (x08 ≤ x01) ∧ ((x01 - x18) ≥ 1) ∧ ((x01 - x08) ≤ (t - 1)) ∧ ((x08 - x18) ≤ (t - 1))))) : (((x18 - x08) ≤ (t - 1)) ∨ ((x01 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause10425 (t x01 x08 x18 : ℝ) (h : (((x01 ≤ x08) ∧ (x08 ≤ x18) ∧ ((x18 - x01) ≥ 1) ∧ ((x08 - x01) ≤ (t - 1)) ∧ ((x18 - x08) ≤ (t - 1))) ∨ ((x18 ≤ x08) ∧ (x08 ≤ x01) ∧ ((x01 - x18) ≥ 1) ∧ ((x01 - x08) ≤ (t - 1)) ∧ ((x08 - x18) ≤ (t - 1))))) : (((x18 - x08) ≤ (t - 1)) ∨ ((x08 - x18) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x18 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x18) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause10438 (t x34 x38 x48 : ℝ) : (((x34 + ((-1) * x48)) ≥ 1) ∨ ((x34 + ((-1) * x48)) ≤ (-1)) ∨ (¬ (x34 ≤ x38)) ∨ (¬ (x38 ≤ x48)) ∨ (¬ ((x48 - x34) ≥ 1)) ∨ (¬ ((x38 - x34) ≤ (t - 1))) ∨ (¬ ((x48 - x38) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x48)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x48)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x48 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x38 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1181 t x34 x38 x48
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause10439 (t x34 x38 x48 : ℝ) : (((x34 + ((-1) * x48)) ≤ (-1)) ∨ ((t + ((-1) * x34) + x38) ≥ 1) ∨ (¬ (x34 ≤ x38)) ∨ (¬ (x38 ≤ x48)) ∨ (¬ ((x48 - x34) ≥ 1)) ∨ (¬ ((x38 - x34) ≤ (t - 1))) ∨ (¬ ((x48 - x38) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x48)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x34) + x38) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x48 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x38 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1181 t x34 x38 x48
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause10443 (t x34 x38 x48 : ℝ) : (((x34 + ((-1) * x48)) ≥ 1) ∨ ((t + x34 + ((-1) * x38)) ≥ 1) ∨ (¬ (x34 ≤ x38)) ∨ (¬ (x38 ≤ x48)) ∨ (¬ ((x48 - x34) ≥ 1)) ∨ (¬ ((x38 - x34) ≤ (t - 1))) ∨ (¬ ((x48 - x38) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x48)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x34 + ((-1) * x38)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x48 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x38 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1181 t x34 x38 x48
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause10463 (t x34 x38 x48 : ℝ) : (((x34 + ((-1) * x48)) ≥ 1) ∨ ((x34 + ((-1) * x48)) ≤ (-1)) ∨ (¬ (x48 ≤ x38)) ∨ (¬ (x38 ≤ x34)) ∨ (¬ ((x34 - x48) ≥ 1)) ∨ (¬ ((x34 - x38) ≤ (t - 1))) ∨ (¬ ((x38 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x48)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x48)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x48 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x48) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x38 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1181 t x34 x38 x48
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause10464 (t x34 x38 x48 : ℝ) : (((x34 + ((-1) * x48)) ≤ (-1)) ∨ ((t + ((-1) * x34) + x38) ≥ 1) ∨ (¬ (x48 ≤ x38)) ∨ (¬ (x38 ≤ x34)) ∨ (¬ ((x34 - x48) ≥ 1)) ∨ (¬ ((x34 - x38) ≤ (t - 1))) ∨ (¬ ((x38 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x48)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x34) + x38) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x48 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x48) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x38 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1181 t x34 x38 x48
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause10468 (t x34 x38 x48 : ℝ) : (((x34 + ((-1) * x48)) ≥ 1) ∨ ((t + x34 + ((-1) * x38)) ≥ 1) ∨ (¬ (x48 ≤ x38)) ∨ (¬ (x38 ≤ x34)) ∨ (¬ ((x34 - x48) ≥ 1)) ∨ (¬ ((x34 - x38) ≤ (t - 1))) ∨ (¬ ((x38 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x48)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x34 + ((-1) * x38)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x48 ≤ x38) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x38 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x48) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x38) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x38 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1181 t x34 x38 x48
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause10526 (t x34 x38 x48 : ℝ) (h : (((x34 ≤ x38) ∧ (x38 ≤ x48) ∧ ((x48 - x34) ≥ 1) ∧ ((x38 - x34) ≤ (t - 1)) ∧ ((x48 - x38) ≤ (t - 1))) ∨ ((x48 ≤ x38) ∧ (x38 ≤ x34) ∧ ((x34 - x48) ≥ 1) ∧ ((x34 - x38) ≤ (t - 1)) ∧ ((x38 - x48) ≤ (t - 1))))) : ((x34 ≤ x38) ∨ (x48 ≤ x38)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x34 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x38) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause10527 (t x34 x38 x48 : ℝ) (h : (((x34 ≤ x38) ∧ (x38 ≤ x48) ∧ ((x48 - x34) ≥ 1) ∧ ((x38 - x34) ≤ (t - 1)) ∧ ((x48 - x38) ≤ (t - 1))) ∨ ((x48 ≤ x38) ∧ (x38 ≤ x34) ∧ ((x34 - x48) ≥ 1) ∧ ((x34 - x38) ≤ (t - 1)) ∧ ((x38 - x48) ≤ (t - 1))))) : ((x34 ≤ x38) ∨ (x38 ≤ x34)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x34 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x34) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause10528 (t x34 x38 x48 : ℝ) (h : (((x34 ≤ x38) ∧ (x38 ≤ x48) ∧ ((x48 - x34) ≥ 1) ∧ ((x38 - x34) ≤ (t - 1)) ∧ ((x48 - x38) ≤ (t - 1))) ∨ ((x48 ≤ x38) ∧ (x38 ≤ x34) ∧ ((x34 - x48) ≥ 1) ∧ ((x34 - x38) ≤ (t - 1)) ∧ ((x38 - x48) ≤ (t - 1))))) : ((x34 ≤ x38) ∨ ((x34 - x48) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x34 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x48) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause10529 (t x34 x38 x48 : ℝ) (h : (((x34 ≤ x38) ∧ (x38 ≤ x48) ∧ ((x48 - x34) ≥ 1) ∧ ((x38 - x34) ≤ (t - 1)) ∧ ((x48 - x38) ≤ (t - 1))) ∨ ((x48 ≤ x38) ∧ (x38 ≤ x34) ∧ ((x34 - x48) ≥ 1) ∧ ((x34 - x38) ≤ (t - 1)) ∧ ((x38 - x48) ≤ (t - 1))))) : ((x34 ≤ x38) ∨ ((x34 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x34 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause10530 (t x34 x38 x48 : ℝ) (h : (((x34 ≤ x38) ∧ (x38 ≤ x48) ∧ ((x48 - x34) ≥ 1) ∧ ((x38 - x34) ≤ (t - 1)) ∧ ((x48 - x38) ≤ (t - 1))) ∨ ((x48 ≤ x38) ∧ (x38 ≤ x34) ∧ ((x34 - x48) ≥ 1) ∧ ((x34 - x38) ≤ (t - 1)) ∧ ((x38 - x48) ≤ (t - 1))))) : ((x34 ≤ x38) ∨ ((x38 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x34 ≤ x38) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause10531 (t x34 x38 x48 : ℝ) (h : (((x34 ≤ x38) ∧ (x38 ≤ x48) ∧ ((x48 - x34) ≥ 1) ∧ ((x38 - x34) ≤ (t - 1)) ∧ ((x48 - x38) ≤ (t - 1))) ∨ ((x48 ≤ x38) ∧ (x38 ≤ x34) ∧ ((x34 - x48) ≥ 1) ∧ ((x34 - x38) ≤ (t - 1)) ∧ ((x38 - x48) ≤ (t - 1))))) : ((x38 ≤ x48) ∨ (x48 ≤ x38)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x38 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x38) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause10532 (t x34 x38 x48 : ℝ) (h : (((x34 ≤ x38) ∧ (x38 ≤ x48) ∧ ((x48 - x34) ≥ 1) ∧ ((x38 - x34) ≤ (t - 1)) ∧ ((x48 - x38) ≤ (t - 1))) ∨ ((x48 ≤ x38) ∧ (x38 ≤ x34) ∧ ((x34 - x48) ≥ 1) ∧ ((x34 - x38) ≤ (t - 1)) ∧ ((x38 - x48) ≤ (t - 1))))) : ((x38 ≤ x48) ∨ (x38 ≤ x34)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x38 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x34) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause10533 (t x34 x38 x48 : ℝ) (h : (((x34 ≤ x38) ∧ (x38 ≤ x48) ∧ ((x48 - x34) ≥ 1) ∧ ((x38 - x34) ≤ (t - 1)) ∧ ((x48 - x38) ≤ (t - 1))) ∨ ((x48 ≤ x38) ∧ (x38 ≤ x34) ∧ ((x34 - x48) ≥ 1) ∧ ((x34 - x38) ≤ (t - 1)) ∧ ((x38 - x48) ≤ (t - 1))))) : ((x38 ≤ x48) ∨ ((x34 - x48) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x38 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x48) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause10534 (t x34 x38 x48 : ℝ) (h : (((x34 ≤ x38) ∧ (x38 ≤ x48) ∧ ((x48 - x34) ≥ 1) ∧ ((x38 - x34) ≤ (t - 1)) ∧ ((x48 - x38) ≤ (t - 1))) ∨ ((x48 ≤ x38) ∧ (x38 ≤ x34) ∧ ((x34 - x48) ≥ 1) ∧ ((x34 - x38) ≤ (t - 1)) ∧ ((x38 - x48) ≤ (t - 1))))) : ((x38 ≤ x48) ∨ ((x34 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x38 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause10535 (t x34 x38 x48 : ℝ) (h : (((x34 ≤ x38) ∧ (x38 ≤ x48) ∧ ((x48 - x34) ≥ 1) ∧ ((x38 - x34) ≤ (t - 1)) ∧ ((x48 - x38) ≤ (t - 1))) ∨ ((x48 ≤ x38) ∧ (x38 ≤ x34) ∧ ((x34 - x48) ≥ 1) ∧ ((x34 - x38) ≤ (t - 1)) ∧ ((x38 - x48) ≤ (t - 1))))) : ((x38 ≤ x48) ∨ ((x38 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x38 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause10536 (t x34 x38 x48 : ℝ) (h : (((x34 ≤ x38) ∧ (x38 ≤ x48) ∧ ((x48 - x34) ≥ 1) ∧ ((x38 - x34) ≤ (t - 1)) ∧ ((x48 - x38) ≤ (t - 1))) ∨ ((x48 ≤ x38) ∧ (x38 ≤ x34) ∧ ((x34 - x48) ≥ 1) ∧ ((x34 - x38) ≤ (t - 1)) ∧ ((x38 - x48) ≤ (t - 1))))) : (((x48 - x34) ≥ 1) ∨ (x48 ≤ x38)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x34) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x38) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause10537 (t x34 x38 x48 : ℝ) (h : (((x34 ≤ x38) ∧ (x38 ≤ x48) ∧ ((x48 - x34) ≥ 1) ∧ ((x38 - x34) ≤ (t - 1)) ∧ ((x48 - x38) ≤ (t - 1))) ∨ ((x48 ≤ x38) ∧ (x38 ≤ x34) ∧ ((x34 - x48) ≥ 1) ∧ ((x34 - x38) ≤ (t - 1)) ∧ ((x38 - x48) ≤ (t - 1))))) : (((x48 - x34) ≥ 1) ∨ (x38 ≤ x34)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x34) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x34) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause10538 (t x34 x38 x48 : ℝ) (h : (((x34 ≤ x38) ∧ (x38 ≤ x48) ∧ ((x48 - x34) ≥ 1) ∧ ((x38 - x34) ≤ (t - 1)) ∧ ((x48 - x38) ≤ (t - 1))) ∨ ((x48 ≤ x38) ∧ (x38 ≤ x34) ∧ ((x34 - x48) ≥ 1) ∧ ((x34 - x38) ≤ (t - 1)) ∧ ((x38 - x48) ≤ (t - 1))))) : (((x48 - x34) ≥ 1) ∨ ((x34 - x48) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x34) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x48) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause10539 (t x34 x38 x48 : ℝ) (h : (((x34 ≤ x38) ∧ (x38 ≤ x48) ∧ ((x48 - x34) ≥ 1) ∧ ((x38 - x34) ≤ (t - 1)) ∧ ((x48 - x38) ≤ (t - 1))) ∨ ((x48 ≤ x38) ∧ (x38 ≤ x34) ∧ ((x34 - x48) ≥ 1) ∧ ((x34 - x38) ≤ (t - 1)) ∧ ((x38 - x48) ≤ (t - 1))))) : (((x48 - x34) ≥ 1) ∨ ((x34 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x34) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause10540 (t x34 x38 x48 : ℝ) (h : (((x34 ≤ x38) ∧ (x38 ≤ x48) ∧ ((x48 - x34) ≥ 1) ∧ ((x38 - x34) ≤ (t - 1)) ∧ ((x48 - x38) ≤ (t - 1))) ∨ ((x48 ≤ x38) ∧ (x38 ≤ x34) ∧ ((x34 - x48) ≥ 1) ∧ ((x34 - x38) ≤ (t - 1)) ∧ ((x38 - x48) ≤ (t - 1))))) : (((x48 - x34) ≥ 1) ∨ ((x38 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x34) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause10541 (t x34 x38 x48 : ℝ) (h : (((x34 ≤ x38) ∧ (x38 ≤ x48) ∧ ((x48 - x34) ≥ 1) ∧ ((x38 - x34) ≤ (t - 1)) ∧ ((x48 - x38) ≤ (t - 1))) ∨ ((x48 ≤ x38) ∧ (x38 ≤ x34) ∧ ((x34 - x48) ≥ 1) ∧ ((x34 - x38) ≤ (t - 1)) ∧ ((x38 - x48) ≤ (t - 1))))) : (((x38 - x34) ≤ (t - 1)) ∨ (x48 ≤ x38)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x34) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x38) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause10542 (t x34 x38 x48 : ℝ) (h : (((x34 ≤ x38) ∧ (x38 ≤ x48) ∧ ((x48 - x34) ≥ 1) ∧ ((x38 - x34) ≤ (t - 1)) ∧ ((x48 - x38) ≤ (t - 1))) ∨ ((x48 ≤ x38) ∧ (x38 ≤ x34) ∧ ((x34 - x48) ≥ 1) ∧ ((x34 - x38) ≤ (t - 1)) ∧ ((x38 - x48) ≤ (t - 1))))) : (((x38 - x34) ≤ (t - 1)) ∨ (x38 ≤ x34)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x34) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x34) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause10543 (t x34 x38 x48 : ℝ) (h : (((x34 ≤ x38) ∧ (x38 ≤ x48) ∧ ((x48 - x34) ≥ 1) ∧ ((x38 - x34) ≤ (t - 1)) ∧ ((x48 - x38) ≤ (t - 1))) ∨ ((x48 ≤ x38) ∧ (x38 ≤ x34) ∧ ((x34 - x48) ≥ 1) ∧ ((x34 - x38) ≤ (t - 1)) ∧ ((x38 - x48) ≤ (t - 1))))) : (((x38 - x34) ≤ (t - 1)) ∨ ((x34 - x48) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x34) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x48) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause10544 (t x34 x38 x48 : ℝ) (h : (((x34 ≤ x38) ∧ (x38 ≤ x48) ∧ ((x48 - x34) ≥ 1) ∧ ((x38 - x34) ≤ (t - 1)) ∧ ((x48 - x38) ≤ (t - 1))) ∨ ((x48 ≤ x38) ∧ (x38 ≤ x34) ∧ ((x34 - x48) ≥ 1) ∧ ((x34 - x38) ≤ (t - 1)) ∧ ((x38 - x48) ≤ (t - 1))))) : (((x38 - x34) ≤ (t - 1)) ∨ ((x34 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x34) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause10545 (t x34 x38 x48 : ℝ) (h : (((x34 ≤ x38) ∧ (x38 ≤ x48) ∧ ((x48 - x34) ≥ 1) ∧ ((x38 - x34) ≤ (t - 1)) ∧ ((x48 - x38) ≤ (t - 1))) ∨ ((x48 ≤ x38) ∧ (x38 ≤ x34) ∧ ((x34 - x48) ≥ 1) ∧ ((x34 - x38) ≤ (t - 1)) ∧ ((x38 - x48) ≤ (t - 1))))) : (((x38 - x34) ≤ (t - 1)) ∨ ((x38 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x38 - x34) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause10546 (t x34 x38 x48 : ℝ) (h : (((x34 ≤ x38) ∧ (x38 ≤ x48) ∧ ((x48 - x34) ≥ 1) ∧ ((x38 - x34) ≤ (t - 1)) ∧ ((x48 - x38) ≤ (t - 1))) ∨ ((x48 ≤ x38) ∧ (x38 ≤ x34) ∧ ((x34 - x48) ≥ 1) ∧ ((x34 - x38) ≤ (t - 1)) ∧ ((x38 - x48) ≤ (t - 1))))) : (((x48 - x38) ≤ (t - 1)) ∨ (x48 ≤ x38)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x38) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x38) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause10547 (t x34 x38 x48 : ℝ) (h : (((x34 ≤ x38) ∧ (x38 ≤ x48) ∧ ((x48 - x34) ≥ 1) ∧ ((x38 - x34) ≤ (t - 1)) ∧ ((x48 - x38) ≤ (t - 1))) ∨ ((x48 ≤ x38) ∧ (x38 ≤ x34) ∧ ((x34 - x48) ≥ 1) ∧ ((x34 - x38) ≤ (t - 1)) ∧ ((x38 - x48) ≤ (t - 1))))) : (((x48 - x38) ≤ (t - 1)) ∨ (x38 ≤ x34)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x38) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x38 ≤ x34) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause10548 (t x34 x38 x48 : ℝ) (h : (((x34 ≤ x38) ∧ (x38 ≤ x48) ∧ ((x48 - x34) ≥ 1) ∧ ((x38 - x34) ≤ (t - 1)) ∧ ((x48 - x38) ≤ (t - 1))) ∨ ((x48 ≤ x38) ∧ (x38 ≤ x34) ∧ ((x34 - x48) ≥ 1) ∧ ((x34 - x38) ≤ (t - 1)) ∧ ((x38 - x48) ≤ (t - 1))))) : (((x48 - x38) ≤ (t - 1)) ∨ ((x34 - x48) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x38) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x48) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause10549 (t x34 x38 x48 : ℝ) (h : (((x34 ≤ x38) ∧ (x38 ≤ x48) ∧ ((x48 - x34) ≥ 1) ∧ ((x38 - x34) ≤ (t - 1)) ∧ ((x48 - x38) ≤ (t - 1))) ∨ ((x48 ≤ x38) ∧ (x38 ≤ x34) ∧ ((x34 - x48) ≥ 1) ∧ ((x34 - x38) ≤ (t - 1)) ∧ ((x38 - x48) ≤ (t - 1))))) : (((x48 - x38) ≤ (t - 1)) ∨ ((x34 - x38) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x38) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x38) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause10550 (t x34 x38 x48 : ℝ) (h : (((x34 ≤ x38) ∧ (x38 ≤ x48) ∧ ((x48 - x34) ≥ 1) ∧ ((x38 - x34) ≤ (t - 1)) ∧ ((x48 - x38) ≤ (t - 1))) ∨ ((x48 ≤ x38) ∧ (x38 ≤ x34) ∧ ((x34 - x48) ≥ 1) ∧ ((x34 - x38) ≤ (t - 1)) ∧ ((x38 - x48) ≤ (t - 1))))) : (((x48 - x38) ≤ (t - 1)) ∨ ((x38 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x38) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x38 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause10555 (t x01 x12 x13 x15 x17 x25 x57 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x15)) ≥ 0)) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x17) + x57) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x58)) ≤ (-1)))) := by
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
  have u3 : ((x12 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x17) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x15 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th1189 t x01 x12 x13 x15 x17 x25 x57 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u6 (And.intro u8 (And.intro u2 (And.intro u5 (And.intro u1 (And.intro u4 (And.intro u7 u3)))))))))) h

theorem clause10556 (t x01 x14 x15 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ (x14 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x14 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1190 t x01 x14 x15 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u5 (And.intro u4 (And.intro u6 u2)))))))) h

theorem clause10557 (t x02 x05 x24 x25 x26 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((t + x24 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x24 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1193 t x02 x05 x24 x25 x26 x57
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u2 (And.intro u1 (And.intro u5 (And.intro u6 (And.intro u0 u3))))))) h

theorem clause10558 (t x05 x25 x26 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + ((-1) * x05) + x25) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x26)) ≤ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x05) + x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1194 t x05 x25 x26 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u4 (And.intro u5 u0))))))) h

theorem clause10559 (t x05 x06 x25 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x05) + x25) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x06)) ≥ 0)) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x05) + x25) ≥ 1) := by
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
  have u5 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1195 t x05 x06 x25 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u3 (And.intro u1 u5))))))) h

theorem clause10561 (x36 x38 x56 x68 : ℝ) : ((¬ ((x36 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x38 + ((-1) * x68)) ≥ 0)) ∨ (¬ ((x36 + ((-1) * x38)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x36 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x38 + ((-1) * x68)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x38)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th1210 x36 x38 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u3 u1))))) h

theorem clause10563 (t x01 x13 x17 x34 x37 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x37)) ≤ 0)) ∨ (¬ ((t + x34 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1)))) := by
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
  have u3 : ((x17 + ((-1) * x37)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x34 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1222 t x01 x13 x17 x34 x37
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u5 (And.intro u2 u1))))))) h

theorem clause10564 (x01 x16 x17 : ℝ) : (((x01 + ((-1) * x16)) ≤ (-1)) ∨ (¬ ((x01 + ((-1) * x17)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x17)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x16)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x17)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x16 + ((-1) * x17)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1224 x01 x16 x17
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause10565 (x02 x24 x26 : ℝ) : ((¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x26)) ≥ 0)) ∨ ((x02 + ((-1) * x26)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x02 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1229 x02 x24 x26
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause10566 (x13 x35 x36 : ℝ) : ((¬ ((x35 + ((-1) * x36)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1231 x13 x35 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 u1)))) h

theorem clause10567 (t x01 x12 x15 x35 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ (x35 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
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
  have u3 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1232 t x01 x12 x15 x35 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u4 (And.intro u1 u6)))))))) h

theorem clause10568 (t x02 x03 x24 x35 x47 x58 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x58)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x58) + x78) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
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
  have u4 : ((x35 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x58) + x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1235 t x02 x03 x24 x35 x47 x58 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u1 (And.intro u6 (And.intro u2 (And.intro u4 (And.intro u0 u7))))))))) h

theorem clause10569 (t x06 x07 x46 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x06) + x46) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x07)) ≥ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x07 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x06) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x07)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1237 t x06 x07 x46 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u1 u4))))))) h

theorem clause10570 (x01 x05 x07 : ℝ) : ((¬ ((x01 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x07)) ≥ 0)) ∨ ((x01 + ((-1) * x07)) ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x07)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x01 + ((-1) * x07)) ≥ 0) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1238 x01 x05 x07
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 u0)))) h

theorem clause10572 (x04 x45 x46 : ℝ) : ((¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1240 x04 x45 x46
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u0 u1))) h

theorem clause10573 (t x04 x34 x45 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ (x04 ≥ 0)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x04 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1241 t x04 x34 x45 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u4 (And.intro u6 (And.intro u0 (And.intro u3 u5)))))))) h

theorem clause10574 (t x02 x03 x04 x13 x23 x26 x27 x34 x45 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + x23 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1)) ∨ (¬ ((t + x27 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x23)) ≥ 0) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x23 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x02 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((t + x27 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th1242 t x02 x03 x04 x13 x23 x26 x27 x34 x45 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u6 (And.intro u5 (And.intro u3 (And.intro u9 (And.intro u0 (And.intro u4 (And.intro u8 (And.intro u7 (And.intro u10 u2)))))))))))) h

theorem clause10575 (x04 x24 x45 x46 : ℝ) : ((¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x46)) ≤ 0))) := by
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
  have u2 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th1243 x04 x24 x45 x46
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u2 (And.intro u3 u1)))) h

theorem clause10576 (t x02 x23 x26 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x36)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
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
  have u3 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1245 t x02 x23 x26 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u6 (And.intro u3 (And.intro u4 (And.intro u1 u2)))))))) h

theorem clause10578 (t x01 x15 x17 x25 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x15) + x25) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x57)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x15) + x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th1251 t x01 x15 x17 x25 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u5 (And.intro u2 u3))))))) h

theorem clause10579 (t x01 x05 x12 x15 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x12) + x15) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1)))) := by
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
  have u3 : ((t + ((-1) * x12) + x15) ≥ 1) := by
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
  have h := NineTheoryTrial.th1253 t x01 x05 x12 x15 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u4 u5))))))) h

theorem clause10580 (t x01 x12 x14 x34 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ (x34 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1255 t x01 x12 x14 x34 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u4 (And.intro u5 (And.intro u3 (And.intro u1 u6)))))))) h

theorem clause10581 (t x01 x12 x13 x34 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ (x46 ≥ 0))) := by
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
  have u4 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x46 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1256 t x01 x12 x13 x34 x46
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u1 (And.intro u6 u0))))))) h

theorem clause10582 (t x03 x13 x34 x35 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ (x34 ≥ 0))) := by
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
  have u6 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1258 t x03 x13 x34 x35 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u4 (And.intro u2 (And.intro u1 (And.intro u7 (And.intro u3 u6))))))))) h

theorem clause10583 (x01 x13 x14 : ℝ) : ((¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x14)) ≥ 0)) ∨ ((x01 + ((-1) * x14)) ≥ 1)) := by
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
  have u2 : ¬ ((x01 + ((-1) * x14)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1259 x01 x13 x14
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause10584 (t x01 x12 x13 x35 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1))) := by
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
  have u3 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1260 t x01 x12 x13 x35 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u5 u6)))))))) h

theorem clause10585 (t x01 x13 x34 x36 : ℝ) : ((¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ (x13 ≥ 0)) ∨ ((t + x34 + ((-1) * x36)) ≥ 1) ∨ (¬ ((x34 + ((-1) * x36)) ≥ 0)) ∨ ((t + ((-1) * x01)) ≤ 0)) := by
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
  have u2 : ¬ ((t + x34 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x01)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr hh))))
  have h := NineTheoryTrial.th1264 t x01 x13 x34 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u1 (And.intro u3 u2)))))) h

theorem clause10586 (t x01 x13 x16 x34 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((t + x34 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x36)) ≤ 0))) := by
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
  have u3 : ((t + x34 + ((-1) * x36)) ≥ 1) := by
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
  have h := NineTheoryTrial.th1265 t x01 x13 x16 x34 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u1 (And.intro u3 u4))))))) h

theorem clause10587 (t x01 x12 x13 x16 x34 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((t + x34 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x12) + x16) ≥ 1))) := by
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
  have u4 : ((t + x34 + ((-1) * x36)) ≥ 1) := by
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
  have u7 : ((t + ((-1) * x12) + x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1266 t x01 x12 x13 x16 x34 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u6 (And.intro u1 (And.intro u4 u5))))))))) h

theorem clause10588 (t x03 x13 x34 x36 x56 x67 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x34 ≥ 0))) := by
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
  have u4 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1267 t x03 x13 x34 x36 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u6 (And.intro u2 (And.intro u0 (And.intro u7 u3))))))))) h

theorem clause10589 (t x01 x12 x16 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x46 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x46 ≥ 0) := by
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
  have h := NineTheoryTrial.th1268 t x01 x12 x16 x46 x67
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u4 (And.intro u3 (And.intro u1 (And.intro u0 (And.intro u2 u5))))))) h

theorem clause10590 (x01 x14 x16 : ℝ) : ((¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ ((x01 + ((-1) * x16)) ≥ 1) ∨ (¬ ((x14 + ((-1) * x16)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x16)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1269 x01 x14 x16
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause10591 (t x01 x13 x14 x34 x35 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((t + ((-1) * x34) + x35) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1)))) := by
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
  have u3 : ((x14 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x34) + x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1270 t x01 x13 x14 x34 x35
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u0 (And.intro u4 (And.intro u1 (And.intro u3 u2)))))) h

theorem clause10593 (x03 x34 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th1274 x03 x34
  exact (fun hh => (Or.elim hh (fun hh => hh u0) (fun zz => ((fun hh => hh u1) zz)))) h

theorem clause10595 (t x01 x04 x12 x13 x14 x36 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((t + x36 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x14) ≥ 1))) := by
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
  have u3 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x36 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x12) + x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th1279 t x01 x04 x12 x13 x14 x36 x45 x56
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u8 (And.intro u1 (And.intro u6 (And.intro u5 (And.intro u7 (And.intro u0 (And.intro u2 u4))))))))) h

theorem clause10596 (t x01 x04 x12 x13 x14 x34 x45 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x14) ≥ 1)) ∨ (¬ (x34 ≥ 0))) := by
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
  have u4 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x04 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x12) + x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th1281 t x01 x04 x12 x13 x14 x34 x45 x56 x67
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u6 (And.intro u3 (And.intro u9 (And.intro u1 (And.intro u8 (And.intro u7 (And.intro u2 (And.intro u5 (And.intro u10 u0))))))))))) h

theorem clause10597 (t x01 x03 x12 x13 x17 x34 x45 x57 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + x17 + ((-1) * x57)) ≥ 1))) := by
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
  have u5 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th1282 t x01 x03 x12 x13 x17 x34 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u2 (And.intro u3 (And.intro u8 (And.intro u4 u7)))))))))) h

theorem clause10598 (t x01 x12 x14 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ (x67 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
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
  have u6 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1285 t x01 x12 x14 x46 x67
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u6 (And.intro u4 u5))))))) h

theorem clause10599 (t x01 x12 x14 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ (x78 ≥ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1))) := by
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
  have u5 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1287 t x01 x12 x14 x47 x78
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u3 (And.intro u5 (And.intro u2 (And.intro u1 (And.intro u0 u4))))))) h

theorem clause10601 (t x01 x12 x17 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ (x47 ≥ 0)) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1290 t x01 x12 x17 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u0 (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u1)))))))) h

theorem clause10602 (x01 x12 x17 : ℝ) : ((¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x17)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x17)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1291 x01 x12 x17
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u0 u2))) h

theorem clause10603 (t x01 x12 x13 x17 x34 x35 x37 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x34) + x35) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x17) ≥ 1))) := by
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
  have u3 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x34) + x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x34 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + ((-1) * x12) + x17) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th1292 t x01 x12 x13 x17 x34 x35 x37 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u8 (And.intro u6 (And.intro u1 (And.intro u2 (And.intro u5 (And.intro u7 u4)))))))))) h

theorem clause10604 (t x01 x07 x12 x13 x17 x37 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((t + x37 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x07 + ((-1) * x17)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x17) ≥ 1)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
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
  have u3 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x37 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 + ((-1) * x17)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x12) + x17) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th1293 t x01 x07 x12 x13 x17 x37 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u7 (And.intro u4 (And.intro u8 (And.intro u5 (And.intro u6 (And.intro u3 u1)))))))))) h

theorem clause10605 (t x13 x35 x37 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ (x35 ≥ 0)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
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
  have h := NineTheoryTrial.th1294 t x13 x35 x37 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u6 u4)))))))) h

theorem clause10606 (x37 x67 x78 : ℝ) : ((¬ ((x37 + ((-1) * x67)) ≥ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x37 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1298 x37 x67 x78
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u1 u2))) h

theorem clause10607 (t x01 x05 x12 x14 x15 x47 x56 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ (x47 ≥ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x12) + x15) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x15)) ≥ 0)) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
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
  have u6 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x12) + x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x05 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th1299 t x01 x05 x12 x14 x15 x47 x56 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u1 (And.intro u4 (And.intro u5 (And.intro u7 (And.intro u3 (And.intro u10 (And.intro u6 (And.intro u8 u9)))))))))))) h

theorem clause10608 (t x03 x35 x36 x56 x67 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ (x35 ≥ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1))) := by
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
  have u3 : (x35 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1300 t x03 x35 x36 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u6 u5)))))))) h

theorem clause10609 (t x01 x12 x13 x15 x35 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((t + x35 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x15) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
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
  have u3 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x35 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x12) + x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1302 t x01 x12 x13 x15 x35 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u6 (And.intro u3 (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u4 u7))))))))) h

theorem clause10610 (t x01 x12 x13 x35 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ (x57 ≥ 0))) := by
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
  have u4 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x57 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1303 t x01 x12 x13 x35 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u6 (And.intro u5 (And.intro u3 (And.intro u4 (And.intro u1 u2)))))))) h

theorem clause10611 (t x01 x12 x15 x25 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1))) ∨ (¬ (x25 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x15 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x25 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1306 t x01 x12 x15 x25 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u1 (And.intro u2 (And.intro u3 (And.intro u0 u6)))))))) h

theorem clause10612 (t x01 x04 x06 x12 x14 x15 x46 x56 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x14) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x57)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
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
  have u6 : ((x04 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x12) + x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x56 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x15 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th1307 t x01 x04 x06 x12 x14 x15 x46 x56 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u7 (And.intro u1 (And.intro u8 (And.intro u9 (And.intro u10 (And.intro u6 u3)))))))))))) h

theorem clause10613 (t x01 x04 x12 x14 x15 x46 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x14) ≥ 1)) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
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
  have u4 : ((x04 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x12) + x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
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
  have h := NineTheoryTrial.th1309 t x01 x04 x12 x14 x15 x46 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u5 (And.intro u8 (And.intro u7 (And.intro u4 (And.intro u1 (And.intro u0 (And.intro u3 u2)))))))))) h

theorem clause10614 (x06 x56 x67 : ℝ) : ((¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x56)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1311 x06 x56 x67
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 u0))) h

theorem clause10617 (t x01 x12 x15 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ (x67 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
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
  have h := NineTheoryTrial.th1314 t x01 x12 x15 x56 x67
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u2 (And.intro u1 (And.intro u6 (And.intro u0 (And.intro u5 u3))))))) h

theorem clause10618 (t x24 x45 x46 x56 x57 : ℝ) : ((¬ ((x46 + ((-1) * x56)) ≤ 0)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x46 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x56) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1316 t x24 x45 x46 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u4 (And.intro u2 (And.intro u3 u0))))))) h

theorem clause10619 (t x01 x16 x17 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x16) + x56) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x67)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x16) + x56) ≥ 1) := by
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
  have h := NineTheoryTrial.th1318 t x01 x16 x17 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u4 (And.intro u2 (And.intro u0 u1))))))) h

theorem clause10620 (t x01 x12 x16 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
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
  have u3 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
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
  have h := NineTheoryTrial.th1319 t x01 x12 x16 x56 x67
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u2 (And.intro u6 (And.intro u3 (And.intro u0 (And.intro u4 u1))))))) h

theorem clause10621 (x06 x16 x67 : ℝ) : ((¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x16)) ≤ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x06 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1320 x06 x16 x67
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u0 u2))) h

theorem clause10622 (t x01 x06 x12 x16 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x06)) ≥ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x12) + x16) ≥ 1))) := by
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
  have u3 : ((x01 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x12) + x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1321 t x01 x06 x12 x16 x67
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u0 u2)))))) h

theorem clause10623 (x25 x56 x57 : ℝ) : ((¬ ((x56 + ((-1) * x57)) ≤ 0)) ∨ ((x25 + ((-1) * x56)) ≥ 1) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x56 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1322 x25 x56 x57
  exact (fun hh => u1 (hh (And.intro u0 u2))) h

theorem clause10624 (t x02 x03 x24 x36 x45 x57 x67 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x03) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x02) + x03) ≥ 1) := by
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
  have u5 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th1325 t x02 x03 x24 x36 x45 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u7 (And.intro u2 u5))))))))) h

theorem clause10625 (x01 x16 x17 : ℝ) : (((x01 + ((-1) * x16)) ≥ 1) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x17)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x16)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x16 + ((-1) * x17)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1326 x01 x16 x17
  exact (fun hh => u0 (hh (And.intro u2 u1))) h

theorem clause10631 (t x04 x23 x24 x34 x37 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x34) + x37) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x37)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th1332 t x04 x23 x24 x34 x37 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u6 (And.intro u5 (And.intro u1 u2)))))))) h

theorem clause10633 (t x03 x12 x13 x15 x25 x34 x47 x56 x58 x78 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x15)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x15 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x58)) ≤ (-1)))) := by
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
  have u4 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x15 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))))
  have u11 : ((x25 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))))
  have h := NineTheoryTrial.th1340 t x03 x12 x13 x15 x25 x34 x47 x56 x58 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u7 (And.intro u6 (And.intro u11 (And.intro u10 (And.intro u1 (And.intro u8 (And.intro u9 u5))))))))))))) h

theorem clause10634 (x25 x56 x58 : ℝ) : ((¬ ((x56 + ((-1) * x58)) ≥ 0)) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x56 + ((-1) * x58)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x25 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1341 x25 x56 x58
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u2 u1))) h

theorem clause10635 (t x01 x15 x16 x56 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((t + x56 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x56 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x16 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1342 t x01 x15 x16 x56 x58
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u2 u3))))))) h

theorem clause10636 (x06 x16 x26 x67 : ℝ) : ((¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x16)) ≥ 0)) ∨ ((x26 + ((-1) * x67)) ≤ (-1)) ∨ (¬ ((x16 + ((-1) * x26)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x06 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x26 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x16 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th1343 x06 x16 x26 x67
  exact (fun hh => u2 (hh (And.intro u1 (And.intro u3 u0)))) h

theorem clause10637 (t x01 x12 x25 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ ((t + ((-1) * x78)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1347 t x01 x12 x25 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u3 (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u4 u2)))))))) h

theorem clause10638 (t x07 x16 x17 x46 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + x16 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x07 + ((-1) * x17)) ≥ 0)) ∨ (¬ ((x16 + ((-1) * x17)) ≤ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x16 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x07 + ((-1) * x17)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 + ((-1) * x17)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1349 t x07 x16 x17 x46 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u5 (And.intro u4 (And.intro u3 (And.intro u1 (And.intro u0 u2)))))))) h

theorem clause10640 (t x01 x12 x17 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ (x57 ≥ 0)) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x57 ≥ 0) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1351 t x01 x12 x17 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u3 (And.intro u1 (And.intro u5 u6)))))))) h

theorem clause10641 (t x06 x34 x46 x47 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((t + x06 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x67)) ≥ 0))) := by
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
  have u3 : ((t + x06 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1355 t x06 x34 x46 x47 x67
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u4 (And.intro u0 (And.intro u2 (And.intro u3 u5)))))) h

theorem clause10642 (t x01 x03 x04 x12 x13 x16 x34 x46 x48 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((t + x16 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x48)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x48)) ≥ 1))) := by
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
  have u5 : ((x03 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x16 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x04 + ((-1) * x48)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x34 + ((-1) * x48)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th1358 t x01 x03 x04 x12 x13 x16 x34 x46 x48
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u7 (And.intro u4 (And.intro u2 (And.intro u6 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u8 u9))))))))))) h

theorem clause10646 (t x47 x57 x67 : ℝ) : (((t + x47 + ((-1) * x67)) ≥ 1) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x57)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x47 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x47 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1367 t x47 x57 x67
  exact (fun hh => u0 (hh (And.intro u2 u1))) h

theorem clause10647 (x01 x02 x16 x26 : ℝ) : ((¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x26)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x02)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x16 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th1374 x01 x02 x16 x26
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u0 (And.intro u3 u1)))) h

theorem clause10648 (x01 x12 x16 : ℝ) : ((¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x16)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1375 x01 x12 x16
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 u0))) h

theorem clause10650 (x06 x16 x46 : ℝ) : (((x06 + ((-1) * x46)) ≥ 0) ∨ (¬ ((x16 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x16)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 + ((-1) * x46)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ((x16 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1380 x06 x16 x46
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause10651 (x01 x16 : ℝ) : ((¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th1381 x01 x16
  exact (fun hh => (Or.elim hh (fun hh => hh u1) (fun zz => ((fun hh => hh u0) zz)))) h

theorem clause10652 (x02 x24 : ℝ) : ((¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th1383 x02 x24
  exact (fun hh => (Or.elim hh (fun hh => hh u0) (fun zz => ((fun hh => hh u1) zz)))) h

theorem clause10653 (t x02 x03 x24 x36 x45 x56 x67 x78 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x03) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x02) + x03) ≥ 1) := by
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
  have u5 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th1385 t x02 x03 x24 x36 x45 x56 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u5 (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u7 (And.intro u2 (And.intro u8 u9))))))))))) h

theorem clause10654 (t x02 x24 x25 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ (x25 ≥ 0))) := by
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
  have u5 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x25 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1386 t x02 x24 x25 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u4 (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u2 u3)))))))) h

theorem clause10655 (x02 x23 x24 : ℝ) : ((¬ ((x23 + ((-1) * x24)) ≤ 0)) ∨ ((x02 + ((-1) * x23)) ≥ 1) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x23 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1387 x02 x23 x24
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause10656 (t x02 x06 x24 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((t + ((-1) * x02) + x06) ≥ 1))) := by
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
  have u4 : ((x06 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x02) + x06) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1391 t x02 x06 x24 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u3 (And.intro u1 (And.intro u2 u4))))))) h

theorem clause10658 (t x01 x15 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ ((t + ((-1) * x01)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th1393 t x01 x15 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u1 (And.intro u5 (And.intro u0 (And.intro u4 (And.intro u2 u3)))))))) h

theorem clause10659 (t x01 x12 x17 x24 x46 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ (x46 ≥ 0)) ∨ (¬ ((x17 + ((-1) * x47)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1))) := by
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
  have u3 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x46 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1397 t x01 x12 x17 x24 x46 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u4 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u5 u6))))))))) h

theorem clause10661 (t x07 x24 x46 x47 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ (x46 ≥ 0)) ∨ (¬ ((x07 + ((-1) * x47)) ≥ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
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
  have u3 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x46 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1403 t x07 x24 x46 x47 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u2 (And.intro u5 (And.intro u7 (And.intro u6 (And.intro u3 u0))))))))) h

theorem clause10662 (t x01 x02 x04 x16 x24 x45 x47 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x47 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
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
  have u4 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x04)) ≥ 0) := by
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
  have u8 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th1405 t x01 x02 x04 x16 x24 x45 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u3 (And.intro u1 (And.intro u6 (And.intro u7 (And.intro u2 (And.intro u5 (And.intro u0 u8)))))))))) h

theorem clause10663 (t x17 x25 x45 x56 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x25 + ((-1) * x45)) ≥ 0)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ ((t + ((-1) * x17)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x25 + ((-1) * x45)) ≥ 0) := by
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
  have u4 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1406 t x17 x25 x45 x56 x57 x78
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u4 (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u1 u7)))))))) h

theorem clause10664 (t x04 x24 x45 x47 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x04)) ≤ 0)) := by
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
  have u3 : ((x24 + ((-1) * x45)) ≥ 1) := by
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
  have u6 : ¬ ((t + ((-1) * x04)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1407 t x04 x24 x45 x47 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u1 (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u3 u2)))))))) h

theorem clause10666 (x06 x56 x67 : ℝ) : (((x06 + ((-1) * x67)) ≥ 1) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x56)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1413 x06 x56 x67
  exact (fun hh => u0 (hh (And.intro u2 u1))) h

theorem clause10668 (t x01 x14 x15 x45 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((t + ((-1) * x45) + x47) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≤ (-1)))) := by
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
  have u3 : ((x15 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x45) + x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1416 t x01 x14 x15 x45 x47
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u4 (And.intro u3 (And.intro u0 (And.intro u2 u5)))))) h

theorem clause10669 (t x01 x14 x17 x45 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x17 + ((-1) * x47)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x45) + x47) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x17 + ((-1) * x47)) ≥ 0) := by
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
  have u4 : ((t + ((-1) * x45) + x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1417 t x01 x14 x17 x45 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u3 u4))))))) h

theorem clause10670 (t x37 x47 x57 : ℝ) : ((¬ ((t + ((-1) * x37) + x57) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x57)) ≥ 0)) ∨ ((t + ((-1) * x37) + x47) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x37) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x47 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x37) + x47) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1419 t x37 x47 x57
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause10671 (t x05 x14 x45 x46 x56 : ℝ) : ((¬ ((x46 + ((-1) * x56)) ≤ 0)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + ((-1) * x05) + x45) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1))) := by
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
  have u3 : ((t + ((-1) * x05) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1422 t x05 x14 x45 x46 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u4 u2))))))) h

theorem clause10672 (x16 x36 x68 : ℝ) : ((¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x36)) ≤ 0)) ∨ ((x16 + ((-1) * x68)) ≤ (-1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x16 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x16 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1425 x16 x36 x68
  exact (fun hh => u2 (hh (And.intro u1 u0))) h

theorem clause10673 (t x04 x26 x46 x47 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x67)) ≥ 0)) ∨ (¬ ((t + x26 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1)))) := by
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
  have u3 : ((x47 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x26 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1427 t x04 x26 x46 x47 x67
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u4 (And.intro u2 (And.intro u5 (And.intro u3 u0)))))) h

theorem clause10674 (x06 x36 x68 : ℝ) : ((¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x36)) ≤ 0)) ∨ ((x06 + ((-1) * x68)) ≤ (-1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x06 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x06 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1430 x06 x36 x68
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause10675 (t x02 x06 x23 x26 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((t + x23 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x26 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x23 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1432 t x02 x06 x23 x26 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u2 (And.intro u1 (And.intro u3 u4))))))) h

theorem clause10676 (t x02 x23 x26 x46 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ ((t + ((-1) * x46)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x68)) ≤ (-1)))) := by
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
  have u3 : ¬ ((t + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x68)) ≥ 1) := by
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
  have h := NineTheoryTrial.th1433 t x02 x23 x26 x46 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u6 (And.intro u5 (And.intro u4 (And.intro u3 u0)))))))) h

theorem clause10679 (x26 x46 x67 : ℝ) : ((¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x26 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1450 x26 x46 x67
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u2 u1))) h

theorem clause10680 (t x04 x24 x36 x46 x47 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((t + ((-1) * x36) + x46) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x67)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x36) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1451 t x04 x24 x36 x46 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u1 (And.intro u6 (And.intro u5 (And.intro u4 u3)))))))) h

theorem clause10681 (t x01 x16 x26 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x68)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x68)) ≤ (-1))) ∨ (¬ (x01 ≥ 0)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1452 t x01 x16 x26 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u6 (And.intro u2 (And.intro u3 (And.intro u0 u1)))))))) h

theorem clause10682 (t x25 x35 x36 x45 x56 x68 : ℝ) : ((¬ ((x35 + ((-1) * x36)) ≥ 0)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x35) + x45) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1))) := by
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
  have u3 : ((x25 + ((-1) * x45)) ≥ 0) := by
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
  have u6 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1454 t x25 x35 x36 x45 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u2 (And.intro u4 (And.intro u0 (And.intro u1 u6)))))))) h

theorem clause10684 (t x01 x12 x17 x27 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ (x67 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x27)) ≥ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x27 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 + ((-1) * x27)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x27 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1457 t x01 x12 x17 x27 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u7 (And.intro u4 (And.intro u1 (And.intro u5 (And.intro u0 (And.intro u3 u6))))))))) h

theorem clause10685 (t x24 x34 x35 x36 x46 x68 : ℝ) : ((¬ ((x35 + ((-1) * x36)) ≥ 0)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((t + x24 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x36)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x24 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1462 t x24 x34 x35 x36 x46 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u6 (And.intro u1 (And.intro u5 u4)))))))) h

theorem clause10686 (t x02 x03 x25 x36 x56 x67 x68 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x03) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((t + x67 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x02) + x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x67 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1468 t x02 x03 x25 x36 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u5 (And.intro u7 (And.intro u6 (And.intro u0 (And.intro u3 u4))))))))) h

theorem clause10688 (t x01 x13 x24 x34 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ ((t + ((-1) * x24)) ≤ 0) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ (x01 ≥ 0))) := by
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
  have u3 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1475 t x01 x13 x24 x34 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u0 (And.intro u5 (And.intro u4 (And.intro u2 (And.intro u3 u1)))))))) h

theorem clause10689 (t x05 x14 x15 x34 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x14) + x34) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x15)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1))) := by
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
  have u3 : ((x05 + ((-1) * x45)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x15)) ≥ 0) := by
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
  have h := NineTheoryTrial.th1476 t x05 x14 x15 x34 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u6 (And.intro u5 (And.intro u4 u2)))))))) h

theorem clause10690 (t x02 x05 x23 x25 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x23 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
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
  have u3 : ((x02 + ((-1) * x05)) ≤ 0) := by
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
  have h := NineTheoryTrial.th1481 t x02 x05 x23 x25 x57
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u3 (And.intro u4 (And.intro u0 (And.intro u2 u1)))))) h

theorem clause10691 (t x03 x13 x36 : ℝ) : (((t + ((-1) * x13)) ≤ 0) ∨ ((t + x03 + ((-1) * x13)) ≥ 1) ∨ (¬ (x36 ≥ 0)) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x03 + ((-1) * x13)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th1482 t x03 x13 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u1 u2))))) h

theorem clause10692 (x03 x36 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x36)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th1483 x03 x36
  exact (fun hh => (Or.elim hh (fun hh => hh u0) (fun zz => ((fun hh => hh u1) zz)))) h

theorem clause10693 (t x03 x13 x14 x15 x35 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((t + x03 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x15)) ≥ 0)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x03 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th1491 t x03 x13 x14 x15 x35 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u3 (And.intro u1 (And.intro u6 (And.intro u0 u4)))))))) h

theorem clause10694 (x15 x35 x57 : ℝ) : ((¬ ((x15 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x15 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x15 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1492 x15 x35 x57
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u2 u1))) h

theorem clause10695 (t x03 x05 x13 x35 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((t + x03 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1)))) := by
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
  have u3 : ((t + x03 + ((-1) * x13)) ≥ 1) := by
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
  have h := NineTheoryTrial.th1494 t x03 x05 x13 x35 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u1 (And.intro u5 u3))))))) h

theorem clause10696 (t x01 x03 x12 x26 x34 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + ((-1) * x26) + x56) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
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
  have u3 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x26) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1495 t x01 x03 x12 x26 x34 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u3 (And.intro u7 (And.intro u0 (And.intro u4 (And.intro u2 (And.intro u5 u1))))))))) h

theorem clause10697 (t x01 x12 x23 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ (¬ (x01 ≥ 0))) := by
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
  have u3 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1500 t x01 x12 x23 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u3 (And.intro u5 (And.intro u0 (And.intro u4 (And.intro u1 u2)))))))) h

theorem clause10698 (t x23 x26 x34 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x34) + x36) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x26)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x34) + x36) ≥ 1) := by
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
  have h := NineTheoryTrial.th1501 t x23 x26 x34 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u3 (And.intro u1 (And.intro u0 u5))))))) h

theorem clause10699 (t x02 x03 x13 x23 x36 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x13) + x23) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x13) + x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1503 t x02 x03 x13 x23 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u1 u5))))))) h

theorem clause10701 (t x01 x02 x12 x17 x23 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x17) ≥ 1))) := by
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
  have u4 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x12) + x17) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1508 t x01 x02 x12 x17 x23
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u3 (And.intro u4 (And.intro u5 u2))))))) h

theorem clause10702 (t x01 x12 x15 x24 x25 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x24) + x25) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x24) + x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th1510 t x01 x12 x15 x24 x25
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u2 (And.intro u3 u5))))))) h

theorem clause10703 (t x01 x02 x12 x15 x24 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x15) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
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
  have u3 : ((x12 + ((-1) * x24)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1511 t x01 x02 x12 x15 x24
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u0 (And.intro u2 (And.intro u1 u3))))))) h

theorem clause10704 (t x01 x12 x15 x25 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ (x25 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
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
  have u6 : (x25 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1512 t x01 x12 x15 x25 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u6 (And.intro u5 (And.intro u0 (And.intro u1 (And.intro u3 u4)))))))) h

theorem clause10705 (t x01 x03 x15 x34 x45 x56 x57 : ℝ) : ((¬ ((t + ((-1) * x01) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
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
  have h := NineTheoryTrial.th1514 t x01 x03 x15 x34 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u4 (And.intro u7 (And.intro u6 (And.intro u1 (And.intro u0 u2))))))))) h

theorem clause10706 (t x01 x03 x13 : ℝ) : (((t + ((-1) * x01) + x03) ≥ 1) ∨ ((t + ((-1) * x13)) ≤ 0) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ (x03 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x01) + x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x13)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th1515 t x01 x03 x13
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u2 u0))))) h

theorem clause10707 (t x01 x03 x12 x13 x15 x34 x46 x56 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
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
  have u3 : ((x03 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x12) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x46) + x56) ≥ 1) := by
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
  have h := NineTheoryTrial.th1516 t x01 x03 x12 x13 x15 x34 x46 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u6 (And.intro u7 (And.intro u1 (And.intro u3 (And.intro u0 (And.intro u8 (And.intro u4 u2)))))))))) h

theorem clause10708 (t x15 x34 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x56 ≥ 0) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1518 t x15 x34 x45 x56 x57
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u6 (And.intro u0 (And.intro u3 (And.intro u2 (And.intro u4 u1))))))) h

theorem clause10709 (t x01 x12 x15 x25 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x25)) ≥ 0)) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x25)) ≥ 0) := by
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
  have h := NineTheoryTrial.th1519 t x01 x12 x15 x25 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u1 (And.intro u7 (And.intro u3 (And.intro u6 (And.intro u0 u2))))))))) h

theorem clause10711 (t x01 x12 x14 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1))) := by
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
  have h := NineTheoryTrial.th1522 t x01 x12 x14 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u6 (And.intro u5 u4)))))))) h

theorem clause10712 (t x04 x24 x34 x35 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((t + x24 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1)))) := by
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
  have u4 : ((x04 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1523 t x04 x24 x34 x35 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u3 (And.intro u4 (And.intro u6 (And.intro u2 u1)))))))) h

theorem clause10713 (t x01 x12 x15 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
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
  have u6 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1524 t x01 x12 x15 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u2 (And.intro u1 (And.intro u5 (And.intro u0 u6)))))))) h

theorem clause10714 (x07 x17 x78 : ℝ) : ((¬ ((x07 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x07 + ((-1) * x17)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x07 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x07 + ((-1) * x17)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1525 x07 x17 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 u1)))) h

theorem clause10715 (t x01 x15 x16 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
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
  have u6 : ((x16 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1527 t x01 x15 x16 x56 x67
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u4 (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u6 u1))))))) h

theorem clause10716 (t x03 x04 x34 x37 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((t + ((-1) * x34) + x37) ≥ 1))) := by
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
  have u4 : ((x03 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x34) + x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1530 t x03 x04 x34 x37 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u3 (And.intro u2 u0))))))) h

theorem clause10717 (t x15 x34 x45 x56 x58 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1533 t x15 x34 x45 x56 x58
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u6 (And.intro u5 (And.intro u3 (And.intro u2 (And.intro u1 u0))))))) h

theorem clause10718 (t x01 x12 x13 x15 x37 x58 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((t + x58 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x58)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x12) + x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x58 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x15 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1534 t x01 x12 x13 x15 x37 x58 x78
  exact (fun hh => (fun hh => hh u7) (hh (And.intro u4 (And.intro u5 (And.intro u0 (And.intro u6 (And.intro u3 (And.intro u1 u2)))))))) h

theorem clause10721 (t x01 x14 x15 x25 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x25)) ≥ 0)) ∨ (¬ (x45 ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1)) ∨ ((t + ((-1) * x14)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x25)) ≥ 0) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x14)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1537 t x01 x14 x15 x25 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u3 (And.intro u4 (And.intro u0 (And.intro u7 (And.intro u6 u2))))))))) h

theorem clause10722 (x01 x15 x16 : ℝ) : ((¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x16)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x15 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1538 x01 x15 x16
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause10723 (t x01 x13 x14 x34 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((t + ((-1) * x34) + x36) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1)))) := by
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
  have u3 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x34) + x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1539 t x01 x13 x14 x34 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u2 (And.intro u0 (And.intro u5 u3))))))) h

theorem clause10724 (t x05 x06 x35 x56 x57 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ (x56 ≥ 0)) ∨ ((t + ((-1) * x35)) ≤ 0) ∨ (¬ ((x05 + ((-1) * x06)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1541 t x05 x06 x35 x56 x57 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u3 (And.intro u7 (And.intro u2 (And.intro u4 (And.intro u0 (And.intro u5 u6))))))))) h

theorem clause10725 (t x02 x06 x12 x16 x24 x36 x45 x56 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ ((x02 + ((-1) * x12)) ≥ 0) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + ((-1) * x36) + x56) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x16)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((t + ((-1) * x12) + x16) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x12)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
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
  have u5 : ((t + ((-1) * x36) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x06 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x36 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x12) + x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th1542 t x02 x06 x12 x16 x24 x36 x45 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u6 (And.intro u1 (And.intro u5 (And.intro u8 (And.intro u7 u9))))))))))) h

theorem clause10726 (x25 x56 : ℝ) : ((¬ ((x25 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x56)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x25 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x25 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th1544 x25 x56
  exact (fun hh => (Or.elim hh (fun hh => hh u0) (fun zz => ((fun hh => hh u1) zz)))) h

theorem clause10727 (t x01 x03 x12 x13 x17 x35 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + x17 + ((-1) * x67)) ≥ 1))) := by
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
  have u7 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x17 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th1547 t x01 x03 x12 x13 x17 x35 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u1 (And.intro u8 (And.intro u4 (And.intro u5 (And.intro u0 (And.intro u3 (And.intro u2 u6)))))))))) h

theorem clause10728 (x05 x56 x57 : ℝ) : ((¬ ((x56 + ((-1) * x57)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x56 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1550 x05 x56 x57
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u0 u1))) h

theorem clause10731 (x24 x46 x47 : ℝ) : (((x24 + ((-1) * x46)) ≥ 1) ∨ (¬ ((x46 + ((-1) * x47)) ≤ 0)) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x46 + ((-1) * x47)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1556 x24 x46 x47
  exact (fun hh => u0 (hh (And.intro u2 u1))) h

theorem clause10733 (t x01 x05 x12 x15 x16 x46 x56 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x12) + x15) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x15)) ≥ 0)) ∨ (¬ ((t + ((-1) * x67) + x68) ≥ 1))) := by
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
  have u3 : ((x46 + ((-1) * x68)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x12) + x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x05 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + ((-1) * x67) + x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th1558 t x01 x05 x12 x15 x16 x46 x56 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u0 (And.intro u4 (And.intro u1 (And.intro u2 (And.intro u6 (And.intro u8 (And.intro u7 (And.intro u9 u3))))))))))) h

theorem clause10734 (t x35 x45 x46 x56 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x35) + x45) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x35) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1559 t x35 x45 x46 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u1 u4))))))) h

theorem clause10736 (t x05 x07 x35 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((t + x05 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x07)) ≤ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x05 + ((-1) * x35)) ≥ 1) := by
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
  have h := NineTheoryTrial.th1561 t x05 x07 x35 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u2 (And.intro u0 (And.intro u5 u1))))))) h

theorem clause10737 (x07 x47 x78 : ℝ) : (((x47 + ((-1) * x78)) ≤ (-1)) ∨ (¬ ((x07 + ((-1) * x47)) ≥ 0)) ∨ (¬ ((x07 + ((-1) * x78)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ((x07 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x07 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1563 x07 x47 x78
  exact (fun hh => u0 (hh (And.intro u2 u1))) h

theorem clause10738 (t x47 x56 x67 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + x47 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x68 + ((-1) * x78)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
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
  have u4 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x68 + ((-1) * x78)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1565 t x47 x56 x67 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u4 (And.intro u1 (And.intro u5 u3))))))) h

theorem clause10739 (t x01 x13 x14 x16 x46 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((t + x13 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x67) + x68) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x13 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x46)) ≥ 1) := by
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
  have u7 : ((t + ((-1) * x67) + x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1566 t x01 x13 x14 x16 x46 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u5 (And.intro u7 (And.intro u6 (And.intro u0 u2))))))))) h

theorem clause10740 (x05 x56 x57 : ℝ) : ((¬ ((x56 + ((-1) * x57)) ≤ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ ((x05 + ((-1) * x57)) ≤ (-1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x56 + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x05 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1567 x05 x56 x57
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause10741 (t x05 x35 x37 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x05 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x37 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x37)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x05 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x37 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x37)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1570 t x05 x35 x37 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u1 (And.intro u4 u3))))))) h

theorem clause10742 (t x01 x05 x12 x14 x15 x35 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x35) + x45) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x12) + x15) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x15)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x35) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + ((-1) * x12) + x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x05 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th1572 t x01 x05 x12 x14 x15 x35 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u6 (And.intro u4 (And.intro u1 (And.intro u5 (And.intro u3 (And.intro u8 u7)))))))))) h

theorem clause10743 (t x03 x34 x46 x67 x78 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x03 ≥ 0)) ∨ ((t + ((-1) * x78)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≤ (-1)))) := by
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
  have u3 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x03 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x78)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1573 t x03 x34 x46 x67 x78
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u2 (And.intro u4 (And.intro u0 (And.intro u5 (And.intro u6 u1))))))) h

theorem clause10744 (t x01 x03 x04 x12 x13 x15 x34 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + x15 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
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
  have u4 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((t + x15 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th1574 t x01 x03 x04 x12 x13 x15 x34 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u8 (And.intro u4 (And.intro u5 (And.intro u3 (And.intro u0 (And.intro u9 (And.intro u7 (And.intro u2 u1))))))))))) h

theorem clause10745 (t x01 x05 x12 x15 x17 x56 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x12) + x15) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x15)) ≥ 0)) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + ((-1) * x68) + x78) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x56 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x12) + x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x15)) ≥ 0) := by
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
  have h := NineTheoryTrial.th1575 t x01 x05 x12 x15 x17 x56 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u4 (And.intro u7 (And.intro u5 (And.intro u8 (And.intro u1 u6)))))))))) h

theorem clause10746 (t x05 x06 x45 x56 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x05 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x56 + ((-1) * x68)) ≥ 1))) := by
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
  have u3 : ((x06 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1576 t x05 x06 x45 x56 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u2 (And.intro u1 (And.intro u0 u4))))))) h

theorem clause10747 (x02 x12 x24 : ℝ) : ((¬ ((x02 + ((-1) * x12)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1)))) := by
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
  have u2 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1578 x02 x12 x24
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 u0))) h

theorem clause10748 (t x01 x12 x17 x23 x27 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((t + ((-1) * x23) + x27) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x27)) ≥ 0))) := by
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
  have u3 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x23) + x27) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 + ((-1) * x27)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1579 t x01 x12 x17 x23 x27
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u2 (And.intro u4 (And.intro u0 u1))))))) h

theorem clause10749 (x01 x13 x17 : ℝ) : ((¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x17)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x17)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1581 x01 x13 x17
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u0 u2))) h

theorem clause10750 (x13 x23 x37 : ℝ) : ((¬ ((x13 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x37)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x37)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x13 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x37)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1582 x13 x23 x37
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 u1)))) h

theorem clause10753 (t x04 x45 x47 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x57)) ≥ 0))) := by
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
  have u3 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x56) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 + ((-1) * x57)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1589 t x04 x45 x47 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u5 (And.intro u2 (And.intro u3 u4))))))) h

theorem clause10754 (t x01 x03 x04 x12 x13 x15 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
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
  have u4 : ((x03 + ((-1) * x04)) ≤ 0) := by
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
  have u8 : ((x15 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th1590 t x01 x03 x04 x12 x13 x15 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u2 (And.intro u7 (And.intro u4 (And.intro u1 (And.intro u3 (And.intro u0 (And.intro u8 (And.intro u9 u5))))))))))) h

theorem clause10755 (t x14 x15 x34 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x14 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x15)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x14 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1591 t x14 x15 x34 x45 x57
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u0 (And.intro u3 (And.intro u5 (And.intro u2 u1)))))) h

theorem clause10756 (t x01 x03 x04 x12 x13 x15 x34 x45 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((t + x15 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
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
  have u4 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x15 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th1592 t x01 x03 x04 x12 x13 x15 x34 x45 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u3 (And.intro u6 (And.intro u1 (And.intro u7 (And.intro u8 (And.intro u5 (And.intro u9 u4))))))))))) h

theorem clause10757 (t x17 x35 x45 x56 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((x57 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x17 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x17 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1593 t x17 x35 x45 x56 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u4 (And.intro u1 (And.intro u6 (And.intro u5 (And.intro u7 u3))))))))) h

theorem clause10758 (t x34 x45 x46 x56 x57 : ℝ) : ((¬ ((x46 + ((-1) * x56)) ≤ 0)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + ((-1) * x56) + x57) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
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
  have u4 : ((t + ((-1) * x56) + x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1595 t x34 x45 x46 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u3 u4))))))) h

theorem clause10759 (t x01 x14 x16 x34 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x14 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x14 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x14)) ≥ 1) := by
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
  have h := NineTheoryTrial.th1596 t x01 x14 x16 x34 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u5 u2))))))) h

theorem clause10760 (t x01 x16 x17 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x16) + x46) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x67)) ≥ 0))) := by
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
  have u3 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
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
  have h := NineTheoryTrial.th1597 t x01 x16 x17 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u3 (And.intro u5 (And.intro u1 u4))))))) h

theorem clause10761 (t x01 x12 x14 x24 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ (x24 ≥ 0)) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1598 t x01 x12 x14 x24 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u6 (And.intro u3 (And.intro u4 u2)))))))) h

theorem clause10762 (t x04 x05 x14 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x05)) ≤ 0)) ∨ (¬ ((t + x04 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x04 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x45)) ≥ 1) := by
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
  have h := NineTheoryTrial.th1600 t x04 x05 x14 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u3 u4))))))) h

theorem clause10763 (t x01 x15 x16 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((t + x15 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x15 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1601 t x01 x15 x16 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u4 (And.intro u1 u5))))))) h

theorem clause10764 (x01 x14 x15 : ℝ) : (((x01 + ((-1) * x14)) ≥ 1) ∨ (¬ ((x14 + ((-1) * x15)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x14)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1604 x01 x14 x15
  exact (fun hh => u0 (hh (And.intro u2 u1))) h

theorem clause10765 (x03 x34 x37 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x37)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x37)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x37)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x37)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1606 x03 x34 x37
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 u0)))) h

theorem clause10766 (x37 : ℝ) (h : (x37 ≥ 0)) : ((x37 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x37 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause10767 (t x01 x12 x13 x23 x26 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((t + x23 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≤ (-1)))) := by
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
  have u4 : ((t + x23 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1609 t x01 x12 x13 x23 x26
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u0 (And.intro u5 (And.intro u3 u2))))))) h

theorem clause10768 (t x03 x12 x13 x26 x34 x47 x68 x78 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((t + x68 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
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
  have u4 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x68 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th1610 t x03 x12 x13 x26 x34 x47 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u2 (And.intro u1 (And.intro u8 (And.intro u5 (And.intro u3 (And.intro u6 (And.intro u0 u4)))))))))) h

theorem clause10770 (t x01 x16 x18 x26 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x16) + x26) ≥ 1)) ∨ (¬ ((x18 + ((-1) * x68)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x18)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x26 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x16) + x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x18 + ((-1) * x68)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x18)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1615 t x01 x16 x18 x26 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u2 u4))))))) h

theorem clause10772 (t x01 x16 x17 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x67 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x67)) ≥ 0)) ∨ (¬ ((x16 + ((-1) * x68)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x67 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x17 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1620 t x01 x16 x17 x67 x68
  exact (fun hh => (fun hh => hh u5) (hh (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u2 u4)))))) h

theorem clause10773 (t x01 x12 x15 x17 x35 x45 x56 x57 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ ((t + ((-1) * x12) + x15) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x17 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + ((-1) * x12) + x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
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
  have h := NineTheoryTrial.th1622 t x01 x12 x15 x17 x35 x45 x56 x57 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u6 (And.intro u2 (And.intro u7 (And.intro u9 (And.intro u3 (And.intro u8 (And.intro u1 (And.intro u10 (And.intro u4 u5)))))))))))) h

theorem clause10774 (t x01 x03 x12 x13 x16 x34 x47 x67 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x47) + x67) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x16 + ((-1) * x67)) ≥ 1))) := by
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
  have h := NineTheoryTrial.th1623 t x01 x03 x12 x13 x16 x34 x47 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u5 (And.intro u8 (And.intro u7 (And.intro u2 (And.intro u3 (And.intro u1 (And.intro u0 u4)))))))))) h

theorem clause10775 (t x05 x06 x45 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x05 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x06)) ≤ 0))) := by
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
  have u3 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1624 t x05 x06 x45 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u2 u5))))))) h

theorem clause10777 (t x01 x03 x04 x12 x13 x17 x34 x45 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + x17 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1))) := by
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
  have u7 : ((t + x17 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th1628 t x01 x03 x04 x12 x13 x17 x34 x45 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u9 (And.intro u5 (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u8 (And.intro u6 (And.intro u4 u7))))))))))) h

theorem clause10778 (x03 x35 x37 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x37)) ≤ 0)) ∨ ((x03 + ((-1) * x37)) ≤ (-1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x37)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x03 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1629 x03 x35 x37
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause10779 (t x01 x04 x12 x13 x14 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x14)) ≤ 0) := by
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
  have u4 : ((x04 + ((-1) * x45)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1631 t x01 x04 x12 x13 x14 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u6 u5)))))))) h

theorem clause10780 (t x01 x14 x17 x34 x47 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x14) + x34) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x47)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x17)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x14) + x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x17 + ((-1) * x47)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x17)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1632 t x01 x14 x17 x34 x47
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u0 (And.intro u1 (And.intro u3 u2))))))) h

theorem clause10781 (x01 x14 x16 : ℝ) : ((¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x16)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x16)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1633 x01 x14 x16
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 u0)))) h

theorem clause10782 (t x01 x14 x16 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x45 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x45 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x14)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x16 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1634 t x01 x14 x16 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u5 u3))))))) h

theorem clause10783 (t x02 x24 x46 x67 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x78 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x78 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th1635 t x02 x24 x46 x67 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u0 (And.intro u6 (And.intro u3 (And.intro u5 (And.intro u2 u1)))))))) h

theorem clause10784 (x17 x67 x78 : ℝ) : (((x17 + ((-1) * x78)) ≥ 1) ∨ (¬ ((x17 + ((-1) * x67)) ≥ 0)) ∨ (¬ ((x67 + ((-1) * x78)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ((x17 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x67 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1639 x17 x67 x78
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause10785 (t x15 x17 x34 x46 x47 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x78)) ≤ (-1))) ∨ ((t + ((-1) * x46)) ≤ 0) ∨ (¬ ((x15 + ((-1) * x17)) ≤ 0)) ∨ (¬ ((x47 + ((-1) * x78)) ≥ 1)) ∨ (¬ (x15 ≥ 0))) := by
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
  have u3 : ((x17 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x17)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x15 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1643 t x15 x17 x34 x46 x47 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u4 (And.intro u5 (And.intro u1 (And.intro u3 (And.intro u0 (And.intro u6 u2))))))))) h

theorem clause10786 (t x03 x04 x06 x13 x16 x26 x34 x45 x46 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + x26 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x16)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((t + x13 + ((-1) * x16)) ≥ 1))) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x26 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x06 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x06 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x26 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((t + x13 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th1645 t x03 x04 x06 x13 x16 x26 x34 x45 x46 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u3 (And.intro u5 (And.intro u0 (And.intro u1 (And.intro u7 (And.intro u2 (And.intro u10 (And.intro u9 (And.intro u4 u8)))))))))))) h

theorem clause10787 (t x03 x04 x12 x13 x26 x35 x45 x57 x68 x78 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + ((-1) * x12) + x13) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x45)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x57 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + x68 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x26)) ≥ 1))) := by
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
  have u3 : ((x35 + ((-1) * x45)) ≥ 0) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x26 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((t + x68 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))))
  have u10 : ((x12 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))))
  have h := NineTheoryTrial.th1646 t x03 x04 x12 x13 x26 x35 x45 x57 x68 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u10 (And.intro u1 (And.intro u5 (And.intro u8 (And.intro u6 (And.intro u0 (And.intro u9 (And.intro u2 (And.intro u7 u3)))))))))))) h

theorem clause10789 (t x17 x57 x67 : ℝ) : ((¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x17 + ((-1) * x67)) ≥ 0)) ∨ ((t + x17 + ((-1) * x57)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x57) + x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x17 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + x17 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th1652 t x17 x57 x67
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause10790 (t x02 x03 x04 x24 x35 x46 x47 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x02) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((t + x47 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x47)) ≥ 1))) := by
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
  have u4 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x47 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x24 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th1653 t x02 x03 x04 x24 x35 x46 x47 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u1 (And.intro u3 (And.intro u0 (And.intro u7 (And.intro u5 (And.intro u8 (And.intro u4 u2)))))))))) h

theorem clause10791 (t x02 x03 x24 x35 x46 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + ((-1) * x02) + x03) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + ((-1) * x57) + x67) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1)))) := by
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
  have u3 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x67)) ≥ 1) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1654 t x02 x03 x24 x35 x46 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u7 (And.intro u6 (And.intro u4 u1))))))))) h

theorem clause10792 (t x02 x05 x24 x35 x46 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x02) + x05) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((t + x46 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x57)) ≥ 1) := by
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
  have u4 : ((t + ((-1) * x02) + x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x46 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x05 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th1655 t x02 x05 x24 x35 x46 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u5 (And.intro u1 (And.intro u0 (And.intro u7 (And.intro u2 u6))))))))) h

theorem clause10793 (t x01 x15 x16 x35 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≤ (-1))) ∨ (¬ ((t + x15 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x16)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x15 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th1656 t x01 x15 x16 x35 x56
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u3 (And.intro u2 (And.intro u4 (And.intro u0 u5)))))) h

#print axioms clause10793
end NineCNFDirectTrial
