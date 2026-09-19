import Mathlib.Tactic.Tauto

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineRUPTrial

theorem step27080 (p17 p41 p45 p189 p193 p258 : Prop)
    (h26845 : p193 ∨ p189)
    (h26831 : p45 ∨ p41)
    (h17242 : (¬ p17) ∨ (¬ p45) ∨ (¬ p193) ∨ (¬ p258)) : (¬ p17) ∨ p189 ∨ p41 ∨ (¬ p258) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17242 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)

theorem step27081 (p41 p45 p63 p85 p101 p102 p124 p125 p304 p331 p362 p424 p796 : Prop)
    (h26859 : p304 ∨ p124)
    (h26891 : p796 ∨ p424)
    (h26835 : p85 ∨ p63)
    (h26831 : p45 ∨ p41)
    (h26837 : p102 ∨ p101)
    (h26865 : p362 ∨ p125)
    (h18506 : (¬ p45) ∨ (¬ p85) ∨ (¬ p102) ∨ (¬ p304) ∨ (¬ p331) ∨ (¬ p362) ∨ (¬ p796)) : p124 ∨ p424 ∨ p63 ∨ p41 ∨ p101 ∨ (¬ p331) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p424) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u12 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18506 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u8)

theorem step27082 (p3 p12 p41 p45 p192 p226 p980 p1036 : Prop)
    (h26847 : p226 ∨ p3)
    (h26907 : p1036 ∨ p12)
    (h26831 : p45 ∨ p41)
    (h18970 : (¬ p45) ∨ (¬ p192) ∨ (¬ p226) ∨ (¬ p980) ∨ (¬ p1036)) : p3 ∨ p12 ∨ (¬ p980) ∨ (¬ p192) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18970 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)

theorem step27083 (p6 p41 p45 p192 p1207 p1452 p1465 : Prop)
    (h26831 : p45 ∨ p41)
    (h19681 : (¬ p6) ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p1207) ∨ (¬ p1452) ∨ (¬ p1465)) : (¬ p1207) ∨ (¬ p1465) ∨ p41 ∨ (¬ p6) ∨ (¬ p192) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19681 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u1)

theorem step27084 (p12 p41 p45 p89 p169 p189 p193 p918 p928 : Prop)
    (h26831 : p45 ∨ p41)
    (h26845 : p193 ∨ p189)
    (h26901 : p928 ∨ p918)
    (h17422 : (¬ p12) ∨ (¬ p45) ∨ (¬ p89) ∨ (¬ p169) ∨ (¬ p193) ∨ (¬ p928)) : p41 ∨ p189 ∨ (¬ p12) ∨ (¬ p169) ∨ (¬ p89) ∨ p918 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p41) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p169 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17422 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)

theorem step27085 (p12 p41 p45 p192 p225 p556 p1055 : Prop)
    (h26831 : p45 ∨ p41)
    (h18280 : (¬ p12) ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p225) ∨ (¬ p556) ∨ (¬ p1055)) : (¬ p556) ∨ (¬ p1055) ∨ (¬ p192) ∨ (¬ p225) ∨ p41 ∨ (¬ p12) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18280 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u1)

theorem step27087 (p63 p85 p495 p580 : Prop)
    (h26834 : (¬ p63) ∨ (¬ p85))
    (h13630 : p85 ∨ (¬ p495) ∨ (¬ p580)) : (¬ p580) ∨ (¬ p495) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p85) := by
    rcases h26834 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h13630 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)

theorem step27090 (p495 p496 p499 : Prop)
    (h26875 : p499 ∨ p495)
    (h16850 : p496 ∨ (¬ p499)) : p496 ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p496) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr hu)
  have u2 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16850 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)

theorem step27091 (p495 p499 p583 : Prop)
    (h26875 : p499 ∨ p495)
    (h18572 : (¬ p499) ∨ p583) : p495 ∨ p583 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p583) := fun hu => hn (Or.inr hu)
  have u2 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18572 with q0 | q1
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)

theorem step27092 (p12 p495 p499 p633 p1036 p1076 p1077 : Prop)
    (h26907 : p1036 ∨ p12)
    (h26911 : p1077 ∨ p1076)
    (h26875 : p499 ∨ p495)
    (h16773 : (¬ p499) ∨ (¬ p633) ∨ (¬ p1036) ∨ (¬ p1077)) : p12 ∨ p1076 ∨ p495 ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p12) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16773 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step27093 (p495 p499 p633 p980 p983 p1076 p1077 : Prop)
    (h26875 : p499 ∨ p495)
    (h26903 : p983 ∨ p980)
    (h26911 : p1077 ∨ p1076)
    (h17904 : (¬ p499) ∨ (¬ p633) ∨ (¬ p983) ∨ (¬ p1077)) : p495 ∨ p980 ∨ (¬ p633) ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17904 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)

theorem step27095 (p495 p499 p633 p665 p1076 p1077 p1226 p1237 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26911 : p1077 ∨ p1076)
    (h26875 : p499 ∨ p495)
    (h17457 : (¬ p499) ∨ (¬ p633) ∨ (¬ p665) ∨ (¬ p1077) ∨ (¬ p1226) ∨ (¬ p1237) ∨ (¬ p1333)) : p1325 ∨ (¬ p1226) ∨ p1076 ∨ (¬ p633) ∨ (¬ p1237) ∨ p495 ∨ (¬ p665) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17457 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u7)

theorem step27096 (p16 p495 p499 p633 p665 p789 p790 p814 p858 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26897 : p858 ∨ p789)
    (h26893 : p814 ∨ p790)
    (h26875 : p499 ∨ p495)
    (h18040 : (¬ p16) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p665) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1077)) : p1076 ∨ (¬ p633) ∨ (¬ p665) ∨ p789 ∨ (¬ p16) ∨ p790 ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18040 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u7)

theorem step27097 (p495 p499 p637 p1055 p1095 p1097 : Prop)
    (h26875 : p499 ∨ p495)
    (h17041 : (¬ p499) ∨ (¬ p637) ∨ (¬ p1055) ∨ (¬ p1095) ∨ (¬ p1097)) : (¬ p637) ∨ (¬ p1097) ∨ (¬ p1055) ∨ p495 ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p637 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1097 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17041 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)

theorem step27100 (p121 p495 p499 p1611 p1666 : Prop)
    (h26875 : p499 ∨ p495)
    (h17824 : (¬ p121) ∨ (¬ p499) ∨ (¬ p1611) ∨ (¬ p1666)) : (¬ p1666) ∨ (¬ p1611) ∨ (¬ p121) ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1611 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17824 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)

theorem step27101 (p41 p45 p303 p387 p420 p495 p499 p601 p1004 p1035 p1252 p1489 : Prop)
    (h26881 : p601 ∨ p420)
    (h26867 : p387 ∨ p303)
    (h26875 : p499 ∨ p495)
    (h26831 : p45 ∨ p41)
    (h19438 : (¬ p45) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1004) ∨ (¬ p1035) ∨ (¬ p1252) ∨ (¬ p1489)) : (¬ p1489) ∨ (¬ p1004) ∨ p420 ∨ p303 ∨ p495 ∨ (¬ p1252) ∨ (¬ p1035) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1252 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19438 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u11)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u0)

theorem step27102 (p15 p69 p344 p495 p499 p633 : Prop)
    (h26875 : p499 ∨ p495)
    (h26833 : p69 ∨ p15)
    (h19313 : (¬ p69) ∨ (¬ p344) ∨ (¬ p499) ∨ (¬ p633)) : p495 ∨ (¬ p344) ∨ (¬ p633) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19313 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step27104 (p63 p85 p344 p495 p499 p633 : Prop)
    (h26875 : p499 ∨ p495)
    (h26835 : p85 ∨ p63)
    (h16627 : (¬ p85) ∨ (¬ p344) ∨ (¬ p499) ∨ (¬ p633)) : p495 ∨ (¬ p344) ∨ (¬ p633) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16627 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step27105 (p455 p495 p499 p980 p1452 : Prop)
    (h26875 : p499 ∨ p495)
    (h17905 : (¬ p455) ∨ (¬ p499) ∨ (¬ p980) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p980) ∨ p495 ∨ (¬ p455) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17905 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)

theorem step27106 (p495 p499 p633 p790 p1076 p1077 p1124 p1349 p1385 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26875 : p499 ∨ p495)
    (h19179 : (¬ p499) ∨ (¬ p633) ∨ (¬ p790) ∨ (¬ p1077) ∨ (¬ p1124) ∨ (¬ p1349) ∨ (¬ p1385)) : (¬ p1385) ∨ (¬ p790) ∨ (¬ p1124) ∨ (¬ p1349) ∨ (¬ p633) ∨ p1076 ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u8 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19179 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u0)

theorem step27107 (p224 p495 p499 p897 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26875 : p499 ∨ p495)
    (h18755 : (¬ p224) ∨ (¬ p499) ∨ (¬ p897) ∨ (¬ p1099)) : p1096 ∨ (¬ p897) ∨ p495 ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1096) := fun hu => hn (Or.inl hu)
  have u1 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18755 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step27108 (p344 p382 p419 p495 p499 p545 p621 p633 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26875 : p499 ∨ p495)
    (h17461 : (¬ p344) ∨ (¬ p382) ∨ (¬ p499) ∨ (¬ p545) ∨ (¬ p621) ∨ (¬ p633) ∨ (¬ p996)) : p419 ∨ p495 ∨ (¬ p621) ∨ (¬ p545) ∨ (¬ p344) ∨ (¬ p633) ∨ (¬ p382) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p621 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17461 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)

theorem step27109 (p344 p382 p495 p499 p621 p633 p789 p842 : Prop)
    (h26875 : p499 ∨ p495)
    (h18049 : (¬ p344) ∨ (¬ p382) ∨ (¬ p499) ∨ (¬ p621) ∨ (¬ p633) ∨ (¬ p789) ∨ (¬ p842)) : (¬ p789) ∨ p495 ∨ (¬ p344) ∨ (¬ p621) ∨ (¬ p842) ∨ (¬ p382) ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p621 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p842 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18049 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u4)

theorem step27113 (p84 p189 p193 p419 p495 p499 p582 p595 p616 p789 p795 p1195 : Prop)
    (h26845 : p193 ∨ p189)
    (h26883 : p616 ∨ p595)
    (h26875 : p499 ∨ p495)
    (h17750 : (¬ p84) ∨ (¬ p193) ∨ (¬ p419) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p616) ∨ (¬ p789) ∨ (¬ p795) ∨ (¬ p1195)) : (¬ p1195) ∨ (¬ p789) ∨ p189 ∨ p595 ∨ (¬ p582) ∨ (¬ p419) ∨ p495 ∨ (¬ p795) ∨ (¬ p84) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p795 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17750 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u0)

theorem step27114 (p84 p189 p193 p422 p495 p499 p582 p595 p616 p1000 p1256 p1287 : Prop)
    (h26875 : p499 ∨ p495)
    (h26883 : p616 ∨ p595)
    (h26845 : p193 ∨ p189)
    (h26929 : p1256 ∨ p422)
    (h18760 : (¬ p84) ∨ (¬ p193) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p616) ∨ (¬ p1000) ∨ (¬ p1256) ∨ (¬ p1287)) : p495 ∨ (¬ p84) ∨ p595 ∨ (¬ p582) ∨ (¬ p1000) ∨ p189 ∨ (¬ p1287) ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18760 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u6)

theorem step27116 (p41 p45 p63 p85 p135 p495 p499 p579 : Prop)
    (h26875 : p499 ∨ p495)
    (h26831 : p45 ∨ p41)
    (h26835 : p85 ∨ p63)
    (h16734 : (¬ p45) ∨ (¬ p85) ∨ (¬ p135) ∨ (¬ p499) ∨ (¬ p579)) : (¬ p579) ∨ p495 ∨ (¬ p135) ∨ p41 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16734 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step27117 (p15 p69 p101 p495 p499 p633 : Prop)
    (h26833 : p69 ∨ p15)
    (h26875 : p499 ∨ p495)
    (h17766 : (¬ p69) ∨ (¬ p101) ∨ (¬ p499) ∨ (¬ p633)) : (¬ p633) ∨ (¬ p101) ∨ p15 ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17766 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)

theorem step27119 (p10 p15 p69 p420 p495 p499 p601 : Prop)
    (h26875 : p499 ∨ p495)
    (h26833 : p69 ∨ p15)
    (h26881 : p601 ∨ p420)
    (h18737 : (¬ p10) ∨ (¬ p69) ∨ (¬ p499) ∨ (¬ p601)) : p495 ∨ (¬ p10) ∨ p15 ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18737 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)

theorem step27120 (p15 p69 p303 p387 p420 p495 p499 p601 : Prop)
    (h26875 : p499 ∨ p495)
    (h26867 : p387 ∨ p303)
    (h26833 : p69 ∨ p15)
    (h26881 : p601 ∨ p420)
    (h19651 : (¬ p69) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601)) : p495 ∨ p303 ∨ p15 ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19651 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u7)

theorem step27121 (p6 p24 p64 p495 p499 : Prop)
    (h26875 : p499 ∨ p495)
    (h11154 : (¬ p6) ∨ (¬ p24) ∨ (¬ p64) ∨ (¬ p499)) : (¬ p24) ∨ (¬ p64) ∨ (¬ p6) ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h11154 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step27122 (p2 p5 p419 p420 p434 p495 p499 p601 : Prop)
    (h26881 : p601 ∨ p420)
    (h26875 : p499 ∨ p495)
    (h25777 : (¬ p2) ∨ (¬ p419) ∨ (¬ p5) ∨ (¬ p434) ∨ (¬ p499) ∨ (¬ p601)) : (¬ p2) ∨ (¬ p434) ∨ p420 ∨ (¬ p5) ∨ p495 ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25777 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u6)

theorem step27125 (p3 p5 p163 p226 p331 p420 p424 p495 p499 p601 p796 : Prop)
    (h26847 : p226 ∨ p3)
    (h26891 : p796 ∨ p424)
    (h26875 : p499 ∨ p495)
    (h26881 : p601 ∨ p420)
    (h18992 : (¬ p5) ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p331) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p796)) : p3 ∨ p424 ∨ p495 ∨ (¬ p5) ∨ p420 ∨ (¬ p331) ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p424) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18992 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u8)

theorem step27126 (p84 p163 p189 p193 p225 p495 p499 p544 p582 p595 p616 p906 : Prop)
    (h26883 : p616 ∨ p595)
    (h26875 : p499 ∨ p495)
    (h26877 : p544 ∨ p225)
    (h26845 : p193 ∨ p189)
    (h17633 : (¬ p84) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p499) ∨ (¬ p544) ∨ (¬ p582) ∨ (¬ p616) ∨ (¬ p906)) : (¬ p906) ∨ (¬ p84) ∨ p595 ∨ p495 ∨ (¬ p163) ∨ p225 ∨ (¬ p582) ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p906 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h17633 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u0)

theorem step27128 (p23 p101 p102 p495 p499 p635 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26875 : p499 ∨ p495)
    (h26837 : p102 ∨ p101)
    (h16482 : (¬ p23) ∨ (¬ p102) ∨ (¬ p499) ∨ (¬ p635) ∨ (¬ p1099)) : (¬ p635) ∨ p1096 ∨ p495 ∨ p101 ∨ (¬ p23) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p635 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16482 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step27129 (p10 p101 p102 p420 p495 p499 p601 : Prop)
    (h26875 : p499 ∨ p495)
    (h26881 : p601 ∨ p420)
    (h26837 : p102 ∨ p101)
    (h17861 : (¬ p10) ∨ (¬ p102) ∨ (¬ p499) ∨ (¬ p601)) : (¬ p10) ∨ p495 ∨ p420 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17861 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step27130 (p350 p420 p495 p499 p601 p635 p1096 p1099 : Prop)
    (h26881 : p601 ∨ p420)
    (h26875 : p499 ∨ p495)
    (h26913 : p1099 ∨ p1096)
    (h16807 : (¬ p350) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p635) ∨ (¬ p1099)) : (¬ p635) ∨ (¬ p350) ∨ p420 ∨ p495 ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p635 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16807 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u7)

theorem step27132 (p11 p458 p495 p499 p578 p1229 p1232 p1443 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h26935 : p1443 ∨ p11)
    (h26875 : p499 ∨ p495)
    (h19154 : (¬ p458) ∨ (¬ p499) ∨ (¬ p578) ∨ (¬ p1232) ∨ (¬ p1443)) : (¬ p458) ∨ p1229 ∨ p11 ∨ p495 ∨ (¬ p578) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p458 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p578 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19154 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step27133 (p126 p258 p495 p499 p633 : Prop)
    (h26875 : p499 ∨ p495)
    (h18041 : (¬ p126) ∨ (¬ p258) ∨ (¬ p499) ∨ (¬ p633)) : (¬ p258) ∨ (¬ p633) ∨ p495 ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18041 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)

theorem step27134 (p24 p121 p495 p499 p635 p1084 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26875 : p499 ∨ p495)
    (h16827 : (¬ p24) ∨ (¬ p121) ∨ (¬ p499) ∨ (¬ p635) ∨ (¬ p1084) ∨ (¬ p1099)) : p1096 ∨ (¬ p121) ∨ p495 ∨ (¬ p635) ∨ (¬ p1084) ∨ (¬ p24) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1096) := fun hu => hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p635 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16827 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)

theorem step27135 (p10 p121 p323 p455 p495 p499 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26861 : p323 ∨ p10)
    (h26875 : p499 ∨ p495)
    (h19066 : (¬ p323) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p1206)) : p121 ∨ (¬ p455) ∨ p10 ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19066 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)

theorem step27138 (p386 p420 p495 p499 p601 p1325 p1452 : Prop)
    (h26881 : p601 ∨ p420)
    (h26875 : p499 ∨ p495)
    (h19450 : (¬ p386) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1325) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p386) ∨ (¬ p1325) ∨ p420 ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p386 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19450 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)

theorem step27139 (p347 p420 p495 p499 p601 p836 p1055 p1103 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h26881 : p601 ∨ p420)
    (h26875 : p499 ∨ p495)
    (h19915 : (¬ p347) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p836) ∨ (¬ p1055) ∨ (¬ p1103) ∨ (¬ p1116)) : p1115 ∨ (¬ p836) ∨ p420 ∨ (¬ p347) ∨ (¬ p1055) ∨ (¬ p1103) ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1115) := fun hu => hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19915 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)

theorem step27140 (p5 p420 p434 p495 p499 p601 p1140 p1159 p1330 p1465 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26875 : p499 ∨ p495)
    (h26881 : p601 ∨ p420)
    (h17470 : (¬ p5) ∨ (¬ p434) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1159) ∨ (¬ p1330) ∨ (¬ p1465)) : (¬ p434) ∨ p1140 ∨ (¬ p1330) ∨ p495 ∨ p420 ∨ (¬ p1465) ∨ (¬ p5) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1140) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17470 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u5)

theorem step27141 (p16 p420 p434 p495 p499 p601 p1330 p1349 p1489 : Prop)
    (h26881 : p601 ∨ p420)
    (h26875 : p499 ∨ p495)
    (h18166 : (¬ p16) ∨ (¬ p434) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p1489)) : (¬ p434) ∨ (¬ p1489) ∨ (¬ p16) ∨ p420 ∨ p495 ∨ (¬ p1349) ∨ (¬ p1330) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18166 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u1)

theorem step27142 (p16 p224 p347 p420 p495 p499 p601 p657 p789 p790 p814 p858 : Prop)
    (h26887 : p657 ∨ p224)
    (h26875 : p499 ∨ p495)
    (h26881 : p601 ∨ p420)
    (h26897 : p858 ∨ p789)
    (h26893 : p814 ∨ p790)
    (h19790 : (¬ p16) ∨ (¬ p347) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p657) ∨ (¬ p814) ∨ (¬ p858)) : p224 ∨ p495 ∨ (¬ p16) ∨ p420 ∨ (¬ p347) ∨ p789 ∨ p790 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p224) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19790 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u10)

theorem step27143 (p63 p85 p455 p495 p499 p1452 : Prop)
    (h26875 : p499 ∨ p495)
    (h26835 : p85 ∨ p63)
    (h16546 : (¬ p85) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p1452)) : (¬ p1452) ∨ p495 ∨ p63 ∨ (¬ p455) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16546 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step27144 (p63 p85 p121 p455 p495 p499 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26835 : p85 ∨ p63)
    (h26875 : p499 ∨ p495)
    (h16776 : (¬ p85) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p1206)) : p121 ∨ (¬ p455) ∨ p63 ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16776 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)

theorem step27145 (p8 p241 p455 p495 p499 p710 p734 p918 p1335 p1452 : Prop)
    (h26875 : p499 ∨ p495)
    (h26889 : p710 ∨ p8)
    (h20338 : (¬ p241) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p710) ∨ (¬ p734) ∨ (¬ p918) ∨ (¬ p1335) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p734) ∨ (¬ p241) ∨ (¬ p1335) ∨ p495 ∨ (¬ p455) ∨ (¬ p918) ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20338 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u0)

theorem step27147 (p8 p16 p238 p455 p495 p499 p710 p836 p840 p1081 p1115 : Prop)
    (h26889 : p710 ∨ p8)
    (h26895 : p840 ∨ p836)
    (h26875 : p499 ∨ p495)
    (h19053 : (¬ p16) ∨ (¬ p238) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p710) ∨ (¬ p840) ∨ (¬ p1081) ∨ (¬ p1115)) : (¬ p1115) ∨ (¬ p455) ∨ (¬ p16) ∨ p8 ∨ (¬ p1081) ∨ (¬ p238) ∨ p836 ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19053 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u0)

theorem step27148 (p8 p63 p85 p224 p455 p495 p499 p710 p929 p1102 p1325 : Prop)
    (h26875 : p499 ∨ p495)
    (h26889 : p710 ∨ p8)
    (h26835 : p85 ∨ p63)
    (h16552 : (¬ p85) ∨ (¬ p224) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p710) ∨ (¬ p929) ∨ (¬ p1102) ∨ (¬ p1325)) : p495 ∨ (¬ p1102) ∨ (¬ p929) ∨ p8 ∨ (¬ p455) ∨ (¬ p224) ∨ (¬ p1325) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h16552 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u6)

theorem step27150 (p48 p64 p423 p495 p499 p582 p1140 p1159 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26875 : p499 ∨ p495)
    (h18839 : (¬ p48) ∨ (¬ p64) ∨ (¬ p423) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p1159)) : p1140 ∨ (¬ p423) ∨ p495 ∨ (¬ p64) ∨ (¬ p582) ∨ (¬ p48) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18839 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)

theorem step27151 (p15 p24 p50 p69 p134 p495 p499 : Prop)
    (h26875 : p499 ∨ p495)
    (h26833 : p69 ∨ p15)
    (h16771 : (¬ p24) ∨ (¬ p50) ∨ (¬ p69) ∨ (¬ p134) ∨ (¬ p499)) : p495 ∨ p15 ∨ (¬ p24) ∨ (¬ p50) ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p50 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16771 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step27152 (p41 p45 p189 p193 p303 p387 p420 p495 p499 p601 p864 p1349 : Prop)
    (h26881 : p601 ∨ p420)
    (h26831 : p45 ∨ p41)
    (h26867 : p387 ∨ p303)
    (h26875 : p499 ∨ p495)
    (h26845 : p193 ∨ p189)
    (h18393 : (¬ p45) ∨ (¬ p193) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p864) ∨ (¬ p1349)) : (¬ p864) ∨ (¬ p1349) ∨ p420 ∨ p41 ∨ p303 ∨ p495 ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18393 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u1)

theorem step27154 (p17 p83 p495 p499 p579 : Prop)
    (h26875 : p499 ∨ p495)
    (h12599 : (¬ p17) ∨ (¬ p83) ∨ (¬ p499) ∨ (¬ p579)) : (¬ p579) ∨ (¬ p83) ∨ (¬ p17) ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h12599 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step27155 (p11 p258 p288 p455 p495 p499 : Prop)
    (h26855 : p288 ∨ p258)
    (h26875 : p499 ∨ p495)
    (h18584 : (¬ p11) ∨ (¬ p288) ∨ (¬ p455) ∨ (¬ p499)) : (¬ p455) ∨ (¬ p11) ∨ p258 ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18584 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)

theorem step27156 (p63 p85 p126 p301 p420 p495 p499 p601 : Prop)
    (h26857 : p301 ∨ p126)
    (h26881 : p601 ∨ p420)
    (h26875 : p499 ∨ p495)
    (h26835 : p85 ∨ p63)
    (h16663 : (¬ p85) ∨ (¬ p301) ∨ (¬ p499) ∨ (¬ p601)) : p126 ∨ p420 ∨ p495 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p420) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16663 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)

theorem step27157 (p126 p258 p288 p301 p420 p495 p499 p601 : Prop)
    (h26857 : p301 ∨ p126)
    (h26881 : p601 ∨ p420)
    (h26875 : p499 ∨ p495)
    (h26855 : p288 ∨ p258)
    (h17503 : (¬ p288) ∨ (¬ p301) ∨ (¬ p499) ∨ (¬ p601)) : p126 ∨ p420 ∨ p495 ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p420) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17503 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)

theorem step27158 (p10 p101 p323 p495 p499 p633 : Prop)
    (h26861 : p323 ∨ p10)
    (h26875 : p499 ∨ p495)
    (h19185 : (¬ p101) ∨ (¬ p323) ∨ (¬ p499) ∨ (¬ p633)) : (¬ p101) ∨ (¬ p633) ∨ p10 ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19185 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)

theorem step27159 (p495 p499 p595 p597 p616 p633 : Prop)
    (h26875 : p499 ∨ p495)
    (h26883 : p616 ∨ p595)
    (h24157 : (¬ p597) ∨ (¬ p616) ∨ (¬ p499) ∨ (¬ p633)) : (¬ p597) ∨ p495 ∨ (¬ p633) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p597 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h24157 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step27160 (p8 p163 p167 p455 p495 p499 p560 p710 p734 p1335 p1452 : Prop)
    (h26843 : p167 ∨ p163)
    (h26889 : p710 ∨ p8)
    (h26875 : p499 ∨ p495)
    (h18594 : (¬ p167) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p560) ∨ (¬ p710) ∨ (¬ p734) ∨ (¬ p1335) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p1335) ∨ p163 ∨ (¬ p560) ∨ p8 ∨ (¬ p455) ∨ p495 ∨ (¬ p734) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18594 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u0)

theorem step27161 (p5 p110 p163 p167 p422 p495 p499 p633 p1140 p1159 p1256 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26875 : p499 ∨ p495)
    (h26843 : p167 ∨ p163)
    (h26929 : p1256 ∨ p422)
    (h19799 : (¬ p5) ∨ (¬ p110) ∨ (¬ p167) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p1159) ∨ (¬ p1256)) : p1140 ∨ (¬ p110) ∨ (¬ p633) ∨ p495 ∨ (¬ p5) ∨ p163 ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19799 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u10)

theorem step27164 (p16 p455 p495 p499 p790 p814 p1015 p1335 p1452 : Prop)
    (h26875 : p499 ∨ p495)
    (h26893 : p814 ∨ p790)
    (h17856 : (¬ p16) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p814) ∨ (¬ p1015) ∨ (¬ p1335) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p1015) ∨ p495 ∨ p790 ∨ (¬ p455) ∨ (¬ p16) ∨ (¬ p1335) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17856 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u0)

theorem step27165 (p63 p85 p303 p387 p420 p495 p499 p601 : Prop)
    (h26875 : p499 ∨ p495)
    (h26867 : p387 ∨ p303)
    (h26881 : p601 ∨ p420)
    (h26835 : p85 ∨ p63)
    (h16545 : (¬ p85) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601)) : p495 ∨ p303 ∨ p420 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16545 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)

theorem step27166 (p303 p387 p420 p495 p499 p601 p1325 p1333 : Prop)
    (h26867 : p387 ∨ p303)
    (h26931 : p1333 ∨ p1325)
    (h26875 : p499 ∨ p495)
    (h26881 : p601 ∨ p420)
    (h17474 : (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1333)) : p303 ∨ p1325 ∨ p495 ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17474 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)

theorem step27167 (p224 p303 p387 p420 p495 p499 p601 : Prop)
    (h26867 : p387 ∨ p303)
    (h26875 : p499 ∨ p495)
    (h26881 : p601 ∨ p420)
    (h17909 : (¬ p224) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601)) : p303 ∨ p495 ∨ p420 ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17909 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)

theorem step27168 (p303 p387 p420 p495 p499 p601 p836 p1055 p1103 p1115 p1116 : Prop)
    (h26867 : p387 ∨ p303)
    (h26881 : p601 ∨ p420)
    (h26915 : p1116 ∨ p1115)
    (h26875 : p499 ∨ p495)
    (h19377 : (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p836) ∨ (¬ p1055) ∨ (¬ p1103) ∨ (¬ p1116)) : (¬ p1055) ∨ p303 ∨ (¬ p836) ∨ p420 ∨ (¬ p1103) ∨ p1115 ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19377 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u9)

theorem step27169 (p3 p5 p12 p226 p303 p387 p420 p495 p499 p601 p1036 : Prop)
    (h26847 : p226 ∨ p3)
    (h26907 : p1036 ∨ p12)
    (h26881 : p601 ∨ p420)
    (h26867 : p387 ∨ p303)
    (h26875 : p499 ∨ p495)
    (h25778 : (¬ p387) ∨ (¬ p601) ∨ (¬ p5) ∨ (¬ p499) ∨ (¬ p226) ∨ (¬ p1036)) : p3 ∨ p12 ∨ p420 ∨ p303 ∨ p495 ∨ (¬ p5) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25778 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)

theorem step27170 (p3 p5 p134 p163 p226 p303 p387 p420 p495 p499 p601 : Prop)
    (h26847 : p226 ∨ p3)
    (h26867 : p387 ∨ p303)
    (h26875 : p499 ∨ p495)
    (h26881 : p601 ∨ p420)
    (h18172 : (¬ p5) ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601)) : p3 ∨ p303 ∨ (¬ p163) ∨ p495 ∨ (¬ p134) ∨ (¬ p5) ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18172 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u10)

theorem step27172 (p455 p495 p499 p635 p1084 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26875 : p499 ∨ p495)
    (h16593 : (¬ p455) ∨ (¬ p499) ∨ (¬ p635) ∨ (¬ p1084) ∨ (¬ p1099)) : (¬ p635) ∨ p1096 ∨ (¬ p1084) ∨ (¬ p455) ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p635 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16593 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step27174 (p16 p185 p303 p387 p420 p495 p499 p601 p1115 : Prop)
    (h26875 : p499 ∨ p495)
    (h26867 : p387 ∨ p303)
    (h26881 : p601 ∨ p420)
    (h25779 : (¬ p601) ∨ (¬ p387) ∨ (¬ p185) ∨ (¬ p16) ∨ (¬ p1115) ∨ (¬ p499)) : p495 ∨ (¬ p1115) ∨ (¬ p185) ∨ p303 ∨ (¬ p16) ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h25779 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)

theorem step27175 (p16 p185 p224 p228 p455 p495 p499 p836 : Prop)
    (h26875 : p499 ∨ p495)
    (h19924 : (¬ p16) ∨ (¬ p185) ∨ (¬ p224) ∨ (¬ p228) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p836)) : (¬ p836) ∨ (¬ p224) ∨ (¬ p455) ∨ p495 ∨ (¬ p185) ∨ (¬ p228) ∨ (¬ p16) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19924 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u0)

theorem step27176 (p258 p288 p495 p499 p578 p635 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26855 : p288 ∨ p258)
    (h26875 : p499 ∨ p495)
    (h19309 : (¬ p288) ∨ (¬ p499) ∨ (¬ p578) ∨ (¬ p635) ∨ (¬ p1099)) : (¬ p635) ∨ p1096 ∨ (¬ p578) ∨ p258 ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p635 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p578 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19309 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step27177 (p3 p41 p45 p192 p226 p455 p495 p499 p940 p985 p1452 : Prop)
    (h26847 : p226 ∨ p3)
    (h26875 : p499 ∨ p495)
    (h26831 : p45 ∨ p41)
    (h20592 : (¬ p45) ∨ (¬ p192) ∨ (¬ p226) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1452)) : p3 ∨ (¬ p940) ∨ (¬ p1452) ∨ (¬ p192) ∨ (¬ p455) ∨ p495 ∨ (¬ p985) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20592 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u2)

theorem step27178 (p63 p85 p101 p495 p499 p633 : Prop)
    (h26835 : p85 ∨ p63)
    (h26875 : p499 ∨ p495)
    (h16399 : (¬ p85) ∨ (¬ p101) ∨ (¬ p499) ∨ (¬ p633)) : (¬ p633) ∨ (¬ p101) ∨ p63 ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16399 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)

theorem step27179 (p10 p63 p85 p420 p495 p499 p601 : Prop)
    (h26875 : p499 ∨ p495)
    (h26835 : p85 ∨ p63)
    (h26881 : p601 ∨ p420)
    (h16531 : (¬ p10) ∨ (¬ p85) ∨ (¬ p499) ∨ (¬ p601)) : p495 ∨ (¬ p10) ∨ p63 ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16531 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)

theorem step27180 (p12 p225 p303 p387 p420 p495 p499 p601 p1055 p1103 : Prop)
    (h26875 : p499 ∨ p495)
    (h26867 : p387 ∨ p303)
    (h26881 : p601 ∨ p420)
    (h19445 : (¬ p12) ∨ (¬ p225) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1055) ∨ (¬ p1103)) : (¬ p1055) ∨ p495 ∨ (¬ p225) ∨ p303 ∨ (¬ p12) ∨ (¬ p1103) ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19445 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u5)

theorem step27181 (p16 p163 p167 p189 p225 p347 p420 p495 p499 p601 : Prop)
    (h26875 : p499 ∨ p495)
    (h26843 : p167 ∨ p163)
    (h26881 : p601 ∨ p420)
    (h19808 : (¬ p16) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p225) ∨ (¬ p347) ∨ (¬ p499) ∨ (¬ p601)) : (¬ p347) ∨ p495 ∨ p163 ∨ (¬ p189) ∨ (¬ p225) ∨ p420 ∨ (¬ p16) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19808 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u9)

theorem step27182 (p224 p344 p495 p499 p633 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h26875 : p499 ∨ p495)
    (h17477 : (¬ p344) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p657)) : p224 ∨ p495 ∨ (¬ p344) ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p224) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17477 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step27183 (p16 p344 p495 p499 p633 p789 p790 p814 p858 p1325 : Prop)
    (h26897 : p858 ∨ p789)
    (h26875 : p499 ∨ p495)
    (h26893 : p814 ∨ p790)
    (h17857 : (¬ p16) ∨ (¬ p344) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1325)) : (¬ p344) ∨ (¬ p633) ∨ (¬ p1325) ∨ p789 ∨ p495 ∨ (¬ p16) ∨ p790 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17857 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u2)

theorem step27185 (p16 p185 p344 p495 p499 p633 p664 p1115 : Prop)
    (h26875 : p499 ∨ p495)
    (h19312 : (¬ p16) ∨ (¬ p185) ∨ (¬ p344) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p664) ∨ (¬ p1115)) : (¬ p1115) ∨ (¬ p344) ∨ (¬ p185) ∨ (¬ p633) ∨ (¬ p16) ∨ p495 ∨ (¬ p664) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19312 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u0)

theorem step27186 (p5 p495 p499 p533 p633 p756 p1140 p1159 p1465 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26875 : p499 ∨ p495)
    (h19767 : (¬ p5) ∨ (¬ p499) ∨ (¬ p533) ∨ (¬ p633) ∨ (¬ p756) ∨ (¬ p1159) ∨ (¬ p1465)) : (¬ p756) ∨ p1140 ∨ (¬ p5) ∨ (¬ p633) ∨ (¬ p1465) ∨ p495 ∨ (¬ p533) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1140) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19767 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u4)

theorem step27188 (p16 p101 p134 p189 p455 p495 p499 p1084 : Prop)
    (h26875 : p499 ∨ p495)
    (h18431 : (¬ p16) ∨ (¬ p101) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p1084)) : (¬ p101) ∨ (¬ p1084) ∨ (¬ p189) ∨ p495 ∨ (¬ p134) ∨ (¬ p16) ∨ (¬ p455) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18431 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step27189 (p63 p85 p495 p499 p633 p1076 p1077 : Prop)
    (h26875 : p499 ∨ p495)
    (h26911 : p1077 ∨ p1076)
    (h26835 : p85 ∨ p63)
    (h18105 : (¬ p85) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p1077)) : p495 ∨ p1076 ∨ (¬ p633) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18105 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)

theorem step27192 (p16 p189 p303 p387 p420 p422 p495 p499 p601 p1004 : Prop)
    (h26881 : p601 ∨ p420)
    (h26875 : p499 ∨ p495)
    (h26867 : p387 ∨ p303)
    (h18170 : (¬ p16) ∨ (¬ p189) ∨ (¬ p387) ∨ (¬ p422) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1004)) : (¬ p422) ∨ (¬ p1004) ∨ p420 ∨ (¬ p189) ∨ (¬ p16) ∨ p495 ∨ p303 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u9 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18170 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step27193 (p3 p26 p68 p163 p167 p424 p495 p499 p595 p616 p1195 : Prop)
    (h26875 : p499 ∨ p495)
    (h26883 : p616 ∨ p595)
    (h26843 : p167 ∨ p163)
    (h17634 : (¬ p3) ∨ (¬ p26) ∨ (¬ p68) ∨ (¬ p167) ∨ (¬ p424) ∨ (¬ p499) ∨ (¬ p616) ∨ (¬ p1195)) : (¬ p1195) ∨ (¬ p26) ∨ (¬ p3) ∨ (¬ p68) ∨ p495 ∨ p595 ∨ p163 ∨ (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p26 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17634 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u0)

theorem step27195 (p8 p710 p918 p1055 p1061 p1115 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26889 : p710 ∨ p8)
    (h17505 : (¬ p710) ∨ (¬ p918) ∨ (¬ p1061) ∨ (¬ p1115)) : p1055 ∨ (¬ p1115) ∨ (¬ p918) ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1055) := fun hu => hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17505 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)

theorem step27196 (p12 p534 p918 p1036 p1584 : Prop)
    (h26907 : p1036 ∨ p12)
    (h18151 : (¬ p534) ∨ (¬ p918) ∨ (¬ p1036) ∨ (¬ p1584)) : (¬ p534) ∨ (¬ p1584) ∨ (¬ p918) ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18151 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)

theorem step27197 (p41 p918 p1076 p1077 p1115 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h18344 : (¬ p41) ∨ (¬ p918) ∨ (¬ p1077) ∨ (¬ p1115)) : (¬ p1115) ∨ (¬ p918) ∨ p1076 ∨ (¬ p41) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18344 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step27198 (p185 p237 p918 p1022 p1385 p1393 : Prop)
    (h26851 : p237 ∨ p185)
    (h26933 : p1393 ∨ p1385)
    (h18618 : (¬ p237) ∨ (¬ p918) ∨ (¬ p1022) ∨ (¬ p1393)) : (¬ p1022) ∨ p185 ∨ p1385 ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18618 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)

theorem step27199 (p11 p576 p581 p918 p961 p1443 : Prop)
    (h26879 : p581 ∨ p576)
    (h26935 : p1443 ∨ p11)
    (h19102 : (¬ p581) ∨ (¬ p918) ∨ (¬ p961) ∨ (¬ p1443)) : p576 ∨ (¬ p918) ∨ (¬ p961) ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19102 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)

theorem step27200 (p287 p576 p581 p918 : Prop)
    (h26879 : p581 ∨ p576)
    (h11682 : (¬ p287) ∨ (¬ p581) ∨ (¬ p918)) : p576 ∨ (¬ p287) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : p287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h11682 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)

theorem step27201 (p41 p45 p170 p918 : Prop)
    (h26830 : (¬ p41) ∨ (¬ p45))
    (h12299 : p45 ∨ (¬ p170) ∨ (¬ p918)) : (¬ p918) ∨ (¬ p41) ∨ (¬ p170) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p45) := by
    rcases h26830 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h12299 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)

theorem step27202 (p17 p90 p256 p574 p633 p668 p836 p918 p1076 p1077 : Prop)
    (h26853 : p256 ∨ p17)
    (h26911 : p1077 ∨ p1076)
    (h26586 : p90)
    (h18103 : (¬ p90) ∨ (¬ p256) ∨ (¬ p574) ∨ (¬ p633) ∨ (¬ p668) ∨ (¬ p836) ∨ (¬ p918) ∨ (¬ p1077)) : (¬ p836) ∨ p17 ∨ p1076 ∨ (¬ p918) ∨ (¬ p633) ∨ (¬ p574) ∨ (¬ p668) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p574 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p90 := by
    exact h26586
  rcases h18103 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u8)

theorem step27203 (p11 p90 p227 p266 p287 p918 : Prop)
    (h26586 : p90)
    (h18665 : (¬ p11) ∨ (¬ p90) ∨ (¬ p227) ∨ (¬ p266) ∨ (¬ p287) ∨ (¬ p918)) : (¬ p11) ∨ (¬ p266) ∨ (¬ p918) ∨ (¬ p227) ∨ (¬ p287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p90 := by
    exact h26586
  rcases h18665 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)

theorem step27204 (p63 p85 p367 p382 p434 p739 p918 p1286 p1584 : Prop)
    (h26835 : p85 ∨ p63)
    (h18982 : (¬ p85) ∨ (¬ p367) ∨ (¬ p382) ∨ (¬ p434) ∨ (¬ p739) ∨ (¬ p918) ∨ (¬ p1286) ∨ (¬ p1584)) : (¬ p739) ∨ (¬ p1584) ∨ (¬ p434) ∨ (¬ p382) ∨ (¬ p367) ∨ (¬ p1286) ∨ p63 ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p739 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p367 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18982 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u1)

theorem step27205 (p101 p102 p241 p306 p576 p581 p918 : Prop)
    (h26879 : p581 ∨ p576)
    (h26837 : p102 ∨ p101)
    (h22708 : (¬ p581) ∨ (¬ p306) ∨ (¬ p241) ∨ (¬ p102) ∨ (¬ p918)) : (¬ p241) ∨ p576 ∨ p101 ∨ (¬ p918) ∨ (¬ p306) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h22708 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)

theorem step27206 (p344 p346 p756 p918 p1584 : Prop)
    (h26863 : p346 ∨ p344)
    (h17765 : (¬ p346) ∨ (¬ p756) ∨ (¬ p918) ∨ (¬ p1584)) : (¬ p756) ∨ (¬ p1584) ∨ p344 ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17765 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)

theorem step27207 (p63 p85 p224 p836 p918 : Prop)
    (h26835 : p85 ∨ p63)
    (h19027 : (¬ p85) ∨ (¬ p224) ∨ (¬ p836) ∨ (¬ p918)) : (¬ p836) ∨ (¬ p224) ∨ p63 ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19027 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)

theorem step27208 (p63 p85 p225 p544 p836 p918 : Prop)
    (h26877 : p544 ∨ p225)
    (h26835 : p85 ∨ p63)
    (h16862 : (¬ p85) ∨ (¬ p544) ∨ (¬ p836) ∨ (¬ p918)) : p225 ∨ (¬ p836) ∨ (¬ p918) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16862 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)

theorem step27209 (p126 p185 p237 p576 p581 p918 : Prop)
    (h26851 : p237 ∨ p185)
    (h26879 : p581 ∨ p576)
    (h17502 : (¬ p126) ∨ (¬ p237) ∨ (¬ p581) ∨ (¬ p918)) : p185 ∨ p576 ∨ (¬ p918) ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17502 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)

theorem step27210 (p17 p189 p193 p576 p581 p918 : Prop)
    (h26845 : p193 ∨ p189)
    (h26879 : p581 ∨ p576)
    (h17593 : (¬ p17) ∨ (¬ p193) ∨ (¬ p581) ∨ (¬ p918)) : p189 ∨ (¬ p17) ∨ (¬ p918) ∨ p576 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p189) := fun hu => hn (Or.inl hu)
  have u1 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17593 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)

theorem step27211 (p17 p41 p185 p237 p918 : Prop)
    (h26851 : p237 ∨ p185)
    (h17465 : (¬ p17) ∨ (¬ p41) ∨ (¬ p237) ∨ (¬ p918)) : p185 ∨ (¬ p918) ∨ (¬ p17) ∨ (¬ p41) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17465 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)

theorem step27212 (p12 p41 p166 p918 p980 p1036 : Prop)
    (h26907 : p1036 ∨ p12)
    (h19689 : (¬ p41) ∨ (¬ p166) ∨ (¬ p918) ∨ (¬ p980) ∨ (¬ p1036)) : (¬ p166) ∨ (¬ p918) ∨ (¬ p980) ∨ (¬ p41) ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p166 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19689 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step27213 (p41 p83 p110 p166 p189 p918 p1055 p1061 p1076 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h22709 : (¬ p189) ∨ (¬ p918) ∨ (¬ p83) ∨ (¬ p166) ∨ (¬ p110) ∨ (¬ p1061) ∨ (¬ p41) ∨ (¬ p1076)) : (¬ p166) ∨ p1055 ∨ (¬ p918) ∨ (¬ p83) ∨ (¬ p41) ∨ (¬ p1076) ∨ (¬ p189) ∨ (¬ p110) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p166 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h22709 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)

theorem step27215 (p135 p185 p189 p237 p576 p581 p918 : Prop)
    (h26879 : p581 ∨ p576)
    (h26851 : p237 ∨ p185)
    (h18654 : (¬ p135) ∨ (¬ p189) ∨ (¬ p237) ∨ (¬ p581) ∨ (¬ p918)) : p576 ∨ p185 ∨ (¬ p918) ∨ (¬ p135) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18654 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)

theorem step27217 (p3 p63 p85 p225 p544 p664 p918 p1115 : Prop)
    (h26835 : p85 ∨ p63)
    (h26877 : p544 ∨ p225)
    (h25780 : (¬ p1115) ∨ (¬ p918) ∨ (¬ p85) ∨ (¬ p3) ∨ (¬ p664) ∨ (¬ p544)) : (¬ p1115) ∨ (¬ p3) ∨ p63 ∨ (¬ p918) ∨ p225 ∨ (¬ p664) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25780 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u7)

theorem step27218 (p382 p789 p918 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h18513 : (¬ p382) ∨ (¬ p789) ∨ (¬ p918) ∨ (¬ p1393)) : p1385 ∨ (¬ p789) ∨ (¬ p918) ∨ (¬ p382) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1385) := fun hu => hn (Or.inl hu)
  have u1 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18513 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step27219 (p41 p185 p237 p790 p814 p918 : Prop)
    (h26893 : p814 ∨ p790)
    (h26851 : p237 ∨ p185)
    (h20637 : (¬ p41) ∨ (¬ p237) ∨ (¬ p814) ∨ (¬ p918)) : (¬ p918) ∨ (¬ p41) ∨ p790 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20637 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step27220 (p84 p185 p237 p918 : Prop)
    (h26851 : p237 ∨ p185)
    (h8726 : (¬ p84) ∨ (¬ p237) ∨ (¬ p918)) : p185 ∨ (¬ p918) ∨ (¬ p84) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8726 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)

theorem step27221 (p41 p83 p101 p102 p189 p255 p918 : Prop)
    (h26837 : p102 ∨ p101)
    (h19634 : (¬ p41) ∨ (¬ p83) ∨ (¬ p102) ∨ (¬ p189) ∨ (¬ p255) ∨ (¬ p918)) : (¬ p255) ∨ (¬ p41) ∨ (¬ p189) ∨ (¬ p918) ∨ p101 ∨ (¬ p83) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19634 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u3)

theorem step27222 (p124 p255 p268 p576 p581 p918 : Prop)
    (h26879 : p581 ∨ p576)
    (h17248 : (¬ p124) ∨ (¬ p255) ∨ (¬ p268) ∨ (¬ p581) ∨ (¬ p918)) : (¬ p255) ∨ p576 ∨ (¬ p268) ∨ (¬ p124) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p268 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17248 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)

theorem step27224 (p41 p134 p142 p836 p918 : Prop)
    (h26841 : p142 ∨ p134)
    (h20168 : (¬ p41) ∨ (¬ p142) ∨ (¬ p836) ∨ (¬ p918)) : (¬ p836) ∨ (¬ p918) ∨ (¬ p41) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20168 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)

theorem step27226 (p63 p85 p224 p290 p344 p346 p368 p382 p406 p496 p918 : Prop)
    (h26869 : p406 ∨ p382)
    (h26835 : p85 ∨ p63)
    (h26863 : p346 ∨ p344)
    (h17628 : (¬ p85) ∨ (¬ p224) ∨ (¬ p290) ∨ (¬ p346) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p496) ∨ (¬ p918)) : p382 ∨ (¬ p918) ∨ (¬ p368) ∨ p63 ∨ (¬ p496) ∨ (¬ p224) ∨ p344 ∨ (¬ p290) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p290 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17628 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u1)

theorem step27227 (p3 p63 p85 p225 p290 p344 p346 p544 p918 : Prop)
    (h26877 : p544 ∨ p225)
    (h26863 : p346 ∨ p344)
    (h26835 : p85 ∨ p63)
    (h25781 : (¬ p918) ∨ (¬ p544) ∨ (¬ p85) ∨ (¬ p346) ∨ (¬ p290) ∨ (¬ p3)) : p225 ∨ p344 ∨ (¬ p918) ∨ p63 ∨ (¬ p290) ∨ (¬ p3) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p290 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25781 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)

theorem step27228 (p89 p125 p185 p237 p303 p860 p918 p1273 : Prop)
    (h26851 : p237 ∨ p185)
    (h25782 : (¬ p1273) ∨ (¬ p125) ∨ (¬ p89) ∨ (¬ p303) ∨ (¬ p918) ∨ (¬ p237) ∨ (¬ p860)) : p185 ∨ (¬ p918) ∨ (¬ p1273) ∨ (¬ p89) ∨ (¬ p303) ∨ (¬ p125) ∨ (¬ p860) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p860 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h25782 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u6)

theorem step27229 (p41 p101 p121 p185 p237 p267 p918 p961 : Prop)
    (h26851 : p237 ∨ p185)
    (h19734 : (¬ p41) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p237) ∨ (¬ p267) ∨ (¬ p918) ∨ (¬ p961)) : (¬ p101) ∨ (¬ p918) ∨ (¬ p41) ∨ p185 ∨ (¬ p961) ∨ (¬ p267) ∨ (¬ p121) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p267 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19734 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u4)

theorem step27230 (p14 p44 p90 p189 p193 p225 p544 p727 p918 p1584 : Prop)
    (h26586 : p90)
    (h26845 : p193 ∨ p189)
    (h26877 : p544 ∨ p225)
    (h17383 : (¬ p14) ∨ (¬ p44) ∨ (¬ p90) ∨ (¬ p193) ∨ (¬ p544) ∨ (¬ p727) ∨ (¬ p918) ∨ (¬ p1584)) : (¬ p1584) ∨ (¬ p14) ∨ (¬ p44) ∨ (¬ p918) ∨ p189 ∨ p225 ∨ (¬ p727) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p727 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p90 := by
    exact h26586
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17383 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u0)

theorem step27231 (p10 p121 p420 p577 p601 p918 p980 p1115 : Prop)
    (h26881 : p601 ∨ p420)
    (h19657 : (¬ p10) ∨ (¬ p121) ∨ (¬ p577) ∨ (¬ p601) ∨ (¬ p918) ∨ (¬ p980) ∨ (¬ p1115)) : (¬ p10) ∨ (¬ p1115) ∨ (¬ p980) ∨ (¬ p577) ∨ (¬ p918) ∨ p420 ∨ (¬ p121) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19657 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u1)

theorem step27232 (p6 p18 p19 p48 p156 p192 p918 : Prop)
    (h26829 : p19 ∨ p18)
    (h20029 : (¬ p6) ∨ (¬ p19) ∨ (¬ p48) ∨ (¬ p156) ∨ (¬ p192) ∨ (¬ p918)) : p18 ∨ (¬ p48) ∨ (¬ p192) ∨ (¬ p6) ∨ (¬ p156) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p18) := fun hu => hn (Or.inl hu)
  have u1 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h20029 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u5)

theorem step27233 (p18 p19 p48 p134 p185 p237 p918 : Prop)
    (h26829 : p19 ∨ p18)
    (h26851 : p237 ∨ p185)
    (h20523 : (¬ p19) ∨ (¬ p48) ∨ (¬ p134) ∨ (¬ p237) ∨ (¬ p918)) : (¬ p918) ∨ p18 ∨ p185 ∨ (¬ p48) ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20523 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)

theorem step27234 (p8 p90 p189 p193 p224 p241 p422 p710 p918 p1000 p1256 : Prop)
    (h26929 : p1256 ∨ p422)
    (h26845 : p193 ∨ p189)
    (h26586 : p90)
    (h26889 : p710 ∨ p8)
    (h18667 : (¬ p90) ∨ (¬ p193) ∨ (¬ p224) ∨ (¬ p241) ∨ (¬ p710) ∨ (¬ p918) ∨ (¬ p1000) ∨ (¬ p1256)) : (¬ p241) ∨ p422 ∨ (¬ p918) ∨ p189 ∨ (¬ p224) ∨ p8 ∨ (¬ p1000) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p90 := by
    exact h26586
  have u10 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18667 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)

theorem step27235 (p63 p85 p344 p836 p918 : Prop)
    (h26835 : p85 ∨ p63)
    (h20169 : (¬ p85) ∨ (¬ p344) ∨ (¬ p836) ∨ (¬ p918)) : (¬ p836) ∨ (¬ p344) ∨ p63 ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20169 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)

theorem step27236 (p421 p495 p499 : Prop)
    (h26874 : (¬ p495) ∨ (¬ p499))
    (h20878 : p421 ∨ p499) : p421 ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p421) := fun hu => hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p499) := by
    rcases h26874 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h20878 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step27244 (p126 p420 p579 p601 : Prop)
    (h26880 : (¬ p420) ∨ (¬ p601))
    (h13423 : (¬ p126) ∨ (¬ p579) ∨ p601) : (¬ p420) ∨ (¬ p579) ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p601) := by
    rcases h26880 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h13423 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (u3 q2)

theorem step27245 (p125 p362 p420 p421 p601 : Prop)
    (h26880 : (¬ p420) ∨ (¬ p601))
    (h26865 : p362 ∨ p125)
    (h13699 : (¬ p362) ∨ (¬ p421) ∨ p601) : (¬ p420) ∨ (¬ p421) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p601) := by
    rcases h26880 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u4 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h13699 with q0 | q1 | q2
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (u3 q2)

theorem step27246 (p349 p420 p601 p633 : Prop)
    (h26880 : (¬ p420) ∨ (¬ p601))
    (h12600 : (¬ p349) ∨ p601 ∨ (¬ p633)) : (¬ p420) ∨ (¬ p349) ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p601) := by
    rcases h26880 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h12600 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u2)

theorem step27249 (p2 p161 p227 p234 p481 p498 p1140 p1144 p1159 p1187 p1452 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26873 : p481 ∨ p2)
    (h26919 : p1159 ∨ p1140)
    (h18068 : (¬ p161) ∨ (¬ p227) ∨ (¬ p481) ∨ (¬ p498) ∨ (¬ p1144) ∨ (¬ p1159) ∨ (¬ p1187) ∨ (¬ p1452)) : (¬ p498) ∨ p234 ∨ (¬ p1144) ∨ p2 ∨ (¬ p1452) ∨ p1140 ∨ (¬ p227) ∨ (¬ p161) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p234) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1144 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18068 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u4)

theorem step27250 (p227 p455 p456 p498 p575 p924 p1096 p1099 : Prop)
    (h26871 : p456 ∨ p455)
    (h26913 : p1099 ∨ p1096)
    (h18481 : (¬ p227) ∨ (¬ p456) ∨ (¬ p498) ∨ (¬ p575) ∨ (¬ p924) ∨ (¬ p1099)) : p455 ∨ p1096 ∨ (¬ p575) ∨ (¬ p227) ∨ (¬ p498) ∨ (¬ p924) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p575 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18481 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u7)

theorem step27251 (p125 p362 p420 p498 p640 p1076 p1095 : Prop)
    (h26865 : p362 ∨ p125)
    (h17498 : (¬ p362) ∨ (¬ p420) ∨ (¬ p498) ∨ (¬ p640) ∨ (¬ p1076) ∨ (¬ p1095)) : (¬ p498) ∨ (¬ p420) ∨ p125 ∨ (¬ p1095) ∨ (¬ p1076) ∨ (¬ p640) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p640 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17498 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step27252 (p227 p331 p382 p419 p420 p455 p456 p498 p601 p621 p996 : Prop)
    (h26871 : p456 ∨ p455)
    (h26905 : p996 ∨ p419)
    (h26881 : p601 ∨ p420)
    (h18260 : (¬ p227) ∨ (¬ p331) ∨ (¬ p382) ∨ (¬ p456) ∨ (¬ p498) ∨ (¬ p601) ∨ (¬ p621) ∨ (¬ p996)) : p455 ∨ (¬ p498) ∨ p419 ∨ (¬ p331) ∨ p420 ∨ (¬ p227) ∨ (¬ p382) ∨ (¬ p621) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p621 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18260 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u9)

theorem step27253 (p124 p455 p498 p633 p636 p1452 : Prop)
    (h26885 : p636 ∨ p633)
    (h18062 : (¬ p124) ∨ (¬ p455) ∨ (¬ p498) ∨ (¬ p636) ∨ (¬ p1452)) : (¬ p1452) ∨ p633 ∨ (¬ p455) ∨ (¬ p498) ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p633) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18062 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step27254 (p124 p420 p434 p498 p601 p633 p636 : Prop)
    (h26885 : p636 ∨ p633)
    (h26881 : p601 ∨ p420)
    (h18064 : (¬ p124) ∨ (¬ p434) ∨ (¬ p498) ∨ (¬ p601) ∨ (¬ p636)) : (¬ p434) ∨ (¬ p498) ∨ (¬ p124) ∨ p633 ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p633) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18064 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step27257 (p16 p124 p189 p331 p420 p424 p498 p601 p633 p636 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26885 : p636 ∨ p633)
    (h26881 : p601 ∨ p420)
    (h19852 : (¬ p16) ∨ (¬ p124) ∨ (¬ p189) ∨ (¬ p331) ∨ (¬ p498) ∨ (¬ p601) ∨ (¬ p636) ∨ (¬ p796)) : (¬ p498) ∨ p424 ∨ p633 ∨ (¬ p16) ∨ (¬ p189) ∨ (¬ p124) ∨ p420 ∨ (¬ p331) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p424) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p633) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19852 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u8)

theorem step27258 (p3 p12 p41 p45 p192 p226 p227 p498 p1036 p1325 p1452 : Prop)
    (h26907 : p1036 ∨ p12)
    (h26831 : p45 ∨ p41)
    (h26847 : p226 ∨ p3)
    (h25783 : (¬ p1452) ∨ (¬ p1325) ∨ (¬ p45) ∨ (¬ p1036) ∨ (¬ p498) ∨ (¬ p192) ∨ (¬ p226) ∨ (¬ p227)) : (¬ p1452) ∨ (¬ p498) ∨ (¬ p192) ∨ p12 ∨ (¬ p227) ∨ (¬ p1325) ∨ p41 ∨ p3 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h25783 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u4)

theorem step27259 (p88 p121 p125 p134 p189 p362 p420 p498 p924 p1096 p1099 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26913 : p1099 ∨ p1096)
    (h26865 : p362 ∨ p125)
    (h20019 : (¬ p88) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p498) ∨ (¬ p924) ∨ (¬ p1099) ∨ (¬ p1206)) : p121 ∨ (¬ p189) ∨ (¬ p420) ∨ p1096 ∨ (¬ p88) ∨ (¬ p134) ∨ (¬ p924) ∨ (¬ p498) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h20019 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u9)

theorem step27260 (p3 p14 p43 p187 p227 p229 p422 p498 p1004 p1325 p1452 : Prop)
    (h26849 : p229 ∨ p14)
    (h19389 : (¬ p3) ∨ (¬ p43) ∨ (¬ p187) ∨ (¬ p227) ∨ (¬ p229) ∨ (¬ p422) ∨ (¬ p498) ∨ (¬ p1004) ∨ (¬ p1325) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p422) ∨ p14 ∨ (¬ p187) ∨ (¬ p498) ∨ (¬ p227) ∨ (¬ p1325) ∨ (¬ p1004) ∨ (¬ p3) ∨ (¬ p43) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19389 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u0)

theorem step27263 (p16 p185 p227 p347 p420 p455 p456 p498 p601 p836 : Prop)
    (h26881 : p601 ∨ p420)
    (h26871 : p456 ∨ p455)
    (h19923 : (¬ p16) ∨ (¬ p185) ∨ (¬ p227) ∨ (¬ p347) ∨ (¬ p456) ∨ (¬ p498) ∨ (¬ p601) ∨ (¬ p836)) : (¬ p498) ∨ (¬ p836) ∨ (¬ p185) ∨ (¬ p227) ∨ p420 ∨ (¬ p347) ∨ p455 ∨ (¬ p16) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p455) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19923 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u1)

theorem step27264 (p16 p110 p125 p163 p167 p189 p362 p420 p498 p633 : Prop)
    (h26843 : p167 ∨ p163)
    (h26865 : p362 ∨ p125)
    (h19435 : (¬ p16) ∨ (¬ p110) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p498) ∨ (¬ p633)) : (¬ p420) ∨ (¬ p110) ∨ (¬ p633) ∨ p163 ∨ (¬ p16) ∨ (¬ p498) ∨ (¬ p189) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19435 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u2)

theorem step27267 (p63 p85 p284 p495 p499 p579 p918 : Prop)
    (h26875 : p499 ∨ p495)
    (h26835 : p85 ∨ p63)
    (h19581 : (¬ p85) ∨ (¬ p284) ∨ (¬ p499) ∨ (¬ p579) ∨ (¬ p918)) : (¬ p284) ∨ p495 ∨ (¬ p579) ∨ (¬ p918) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p284 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19581 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)

theorem step27268 (p10 p323 p1209 : Prop)
    (h26861 : p323 ∨ p10)
    (h19893 : (¬ p323) ∨ p1209) : p10 ∨ p1209 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p10) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1209) := fun hu => hn (Or.inr hu)
  have u2 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19893 with q0 | q1
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)

theorem step27269 (p10 p125 p210 p323 p362 : Prop)
    (h26864 : (¬ p125) ∨ (¬ p362))
    (h26861 : p323 ∨ p10)
    (h11313 : (¬ p210) ∨ (¬ p323) ∨ p362) : (¬ p125) ∨ (¬ p210) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p362) := by
    rcases h26864 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u4 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h11313 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (u3 q2)

theorem step27270 (p10 p121 p323 p386 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26861 : p323 ∨ p10)
    (h11608 : (¬ p323) ∨ (¬ p386) ∨ (¬ p1206)) : (¬ p386) ∨ p121 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p386 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u4 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h11608 with q0 | q1 | q2
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)

theorem step27271 (p6 p10 p127 p303 p323 p387 p1325 p1333 : Prop)
    (h26867 : p387 ∨ p303)
    (h26931 : p1333 ∨ p1325)
    (h26861 : p323 ∨ p10)
    (h26839 : p127 ∨ p6)
    (h17581 : (¬ p127) ∨ (¬ p323) ∨ (¬ p387) ∨ (¬ p1333)) : p303 ∨ p1325 ∨ p10 ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17581 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step27272 (p10 p121 p126 p301 p323 p532 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26857 : p301 ∨ p126)
    (h26861 : p323 ∨ p10)
    (h18340 : (¬ p301) ∨ (¬ p323) ∨ (¬ p532) ∨ (¬ p1206)) : p121 ∨ p126 ∨ p10 ∨ (¬ p532) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18340 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step27273 (p10 p121 p161 p323 p532 p1206 p1225 : Prop)
    (h26925 : p1225 ∨ p161)
    (h26923 : p1206 ∨ p121)
    (h26861 : p323 ∨ p10)
    (h19020 : (¬ p323) ∨ (¬ p532) ∨ (¬ p1206) ∨ (¬ p1225)) : p161 ∨ p121 ∨ (¬ p532) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19020 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step27274 (p10 p11 p121 p323 p576 p581 p1206 p1443 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26935 : p1443 ∨ p11)
    (h26861 : p323 ∨ p10)
    (h26879 : p581 ∨ p576)
    (h20340 : (¬ p323) ∨ (¬ p581) ∨ (¬ p1206) ∨ (¬ p1443)) : p121 ∨ p11 ∨ p10 ∨ p576 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p11) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20340 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step27275 (p10 p125 p210 p323 : Prop)
    (h26861 : p323 ∨ p10)
    (h2473 : (¬ p125) ∨ (¬ p210) ∨ (¬ p323)) : (¬ p125) ∨ (¬ p210) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h2473 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step27276 (p10 p126 p140 p323 : Prop)
    (h26861 : p323 ∨ p10)
    (h14549 : p126 ∨ (¬ p140) ∨ (¬ p323)) : p126 ∨ (¬ p140) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h14549 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step27277 (p10 p121 p124 p125 p323 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26861 : p323 ∨ p10)
    (h18372 : (¬ p124) ∨ (¬ p125) ∨ (¬ p323) ∨ (¬ p1206)) : p121 ∨ (¬ p125) ∨ (¬ p124) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18372 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step27278 (p10 p125 p227 p323 p383 p1325 p1333 : Prop)
    (h26861 : p323 ∨ p10)
    (h26931 : p1333 ∨ p1325)
    (h19833 : (¬ p125) ∨ (¬ p227) ∨ (¬ p323) ∨ (¬ p383) ∨ (¬ p1333)) : (¬ p125) ∨ (¬ p383) ∨ p10 ∨ (¬ p227) ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p383 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19833 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)

theorem step27279 (p9 p10 p101 p125 p323 p638 p1055 p1061 p1074 : Prop)
    (h26861 : p323 ∨ p10)
    (h26909 : p1061 ∨ p1055)
    (h25784 : (¬ p1074) ∨ (¬ p125) ∨ (¬ p9) ∨ (¬ p101) ∨ (¬ p638) ∨ (¬ p1061) ∨ (¬ p323)) : (¬ p9) ∨ (¬ p101) ∨ (¬ p125) ∨ p10 ∨ (¬ p638) ∨ (¬ p1074) ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p638 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h25784 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u7)

theorem step27281 (p10 p124 p125 p134 p142 p323 : Prop)
    (h26841 : p142 ∨ p134)
    (h26861 : p323 ∨ p10)
    (h19527 : (¬ p124) ∨ (¬ p125) ∨ (¬ p142) ∨ (¬ p323)) : (¬ p125) ∨ (¬ p124) ∨ p134 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19527 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step27282 (p10 p134 p142 p189 p193 p303 p323 p387 : Prop)
    (h26867 : p387 ∨ p303)
    (h26845 : p193 ∨ p189)
    (h26841 : p142 ∨ p134)
    (h26861 : p323 ∨ p10)
    (h17539 : (¬ p142) ∨ (¬ p193) ∨ (¬ p323) ∨ (¬ p387)) : p303 ∨ p189 ∨ p134 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17539 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)

theorem step27283 (p10 p41 p125 p265 p323 p576 : Prop)
    (h26861 : p323 ∨ p10)
    (h20613 : (¬ p41) ∨ (¬ p125) ∨ (¬ p265) ∨ (¬ p323) ∨ (¬ p576)) : (¬ p576) ∨ (¬ p41) ∨ (¬ p265) ∨ p10 ∨ (¬ p125) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20613 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step27284 (p10 p121 p323 p384 p434 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26861 : p323 ∨ p10)
    (h25785 : (¬ p1206) ∨ (¬ p384) ∨ (¬ p323) ∨ (¬ p434)) : (¬ p434) ∨ p121 ∨ p10 ∨ (¬ p384) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p384 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25785 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)

theorem step27286 (p10 p121 p323 p386 : Prop)
    (h26861 : p323 ∨ p10)
    (h14420 : p121 ∨ (¬ p323) ∨ (¬ p386)) : (¬ p386) ∨ p121 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p386 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h14420 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)

theorem step27287 (p10 p101 p125 p265 p323 p576 : Prop)
    (h26861 : p323 ∨ p10)
    (h20372 : (¬ p101) ∨ (¬ p125) ∨ (¬ p265) ∨ (¬ p323) ∨ (¬ p576)) : (¬ p101) ∨ (¬ p576) ∨ (¬ p265) ∨ p10 ∨ (¬ p125) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20372 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)

theorem step27288 (p10 p18 p19 p67 p125 p206 p323 : Prop)
    (h26829 : p19 ∨ p18)
    (h26861 : p323 ∨ p10)
    (h17331 : (¬ p19) ∨ (¬ p67) ∨ (¬ p125) ∨ (¬ p206) ∨ (¬ p323)) : p18 ∨ (¬ p125) ∨ (¬ p206) ∨ (¬ p67) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p18) := fun hu => hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17331 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)

theorem step27289 (p10 p121 p185 p224 p227 p263 p323 p836 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26861 : p323 ∨ p10)
    (h19052 : (¬ p185) ∨ (¬ p224) ∨ (¬ p227) ∨ (¬ p263) ∨ (¬ p323) ∨ (¬ p836) ∨ (¬ p1206)) : p121 ∨ (¬ p836) ∨ p10 ∨ (¬ p263) ∨ (¬ p227) ∨ (¬ p224) ∨ (¬ p185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p263 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19052 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step27290 (p10 p124 p125 p258 p323 : Prop)
    (h26861 : p323 ∨ p10)
    (h22710 : (¬ p258) ∨ (¬ p125) ∨ (¬ p323) ∨ (¬ p124)) : (¬ p125) ∨ (¬ p258) ∨ (¬ p124) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h22710 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step27292 (p3 p10 p109 p125 p206 p323 : Prop)
    (h26861 : p323 ∨ p10)
    (h19676 : (¬ p3) ∨ (¬ p109) ∨ (¬ p125) ∨ (¬ p206) ∨ (¬ p323)) : (¬ p3) ∨ (¬ p125) ∨ (¬ p206) ∨ p10 ∨ (¬ p109) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19676 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step27293 (p10 p18 p19 p50 p125 p192 p206 p323 : Prop)
    (h26829 : p19 ∨ p18)
    (h26861 : p323 ∨ p10)
    (h17324 : (¬ p19) ∨ (¬ p50) ∨ (¬ p125) ∨ (¬ p192) ∨ (¬ p206) ∨ (¬ p323)) : p18 ∨ (¬ p192) ∨ (¬ p50) ∨ (¬ p125) ∨ (¬ p206) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p18) := fun hu => hn (Or.inl hu)
  have u1 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p50 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17324 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)

theorem step27294 (p6 p10 p127 p163 p167 p195 p224 p323 p347 p382 p560 p657 p709 : Prop)
    (h26843 : p167 ∨ p163)
    (h26861 : p323 ∨ p10)
    (h26839 : p127 ∨ p6)
    (h26887 : p657 ∨ p224)
    (h18574 : (¬ p127) ∨ (¬ p167) ∨ (¬ p195) ∨ (¬ p323) ∨ (¬ p347) ∨ (¬ p382) ∨ (¬ p560) ∨ (¬ p657) ∨ (¬ p709)) : (¬ p560) ∨ p163 ∨ p10 ∨ (¬ p709) ∨ (¬ p382) ∨ p6 ∨ (¬ p195) ∨ p224 ∨ (¬ p347) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u12 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18574 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u11)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u12)
  · exact False.elim (q8 u3)

theorem step27295 (p10 p101 p303 p323 p387 p633 : Prop)
    (h26867 : p387 ∨ p303)
    (h26861 : p323 ∨ p10)
    (h17788 : (¬ p101) ∨ (¬ p323) ∨ (¬ p387) ∨ (¬ p633)) : (¬ p101) ∨ p303 ∨ p10 ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17788 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)

theorem step27296 (p10 p17 p101 p256 p258 p288 p323 : Prop)
    (h26855 : p288 ∨ p258)
    (h26853 : p256 ∨ p17)
    (h26861 : p323 ∨ p10)
    (h17825 : (¬ p101) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p323)) : (¬ p101) ∨ p258 ∨ p17 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p258) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17825 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)

theorem step27300 (p10 p63 p85 p101 p124 p211 p323 p521 p1385 : Prop)
    (h26835 : p85 ∨ p63)
    (h26861 : p323 ∨ p10)
    (h25786 : (¬ p101) ∨ (¬ p211) ∨ (¬ p1385) ∨ (¬ p521) ∨ (¬ p323) ∨ (¬ p124) ∨ (¬ p85)) : (¬ p211) ∨ (¬ p101) ∨ (¬ p124) ∨ p63 ∨ (¬ p521) ∨ p10 ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p521 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h25786 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u7)

theorem step27301 (p10 p83 p101 p124 p211 p323 p790 p814 p918 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h26861 : p323 ∨ p10)
    (h26893 : p814 ∨ p790)
    (h25787 : (¬ p101) ∨ (¬ p918) ∨ (¬ p814) ∨ (¬ p124) ∨ (¬ p1393) ∨ (¬ p211) ∨ (¬ p83) ∨ (¬ p323)) : (¬ p101) ∨ (¬ p83) ∨ p1385 ∨ p10 ∨ (¬ p918) ∨ p790 ∨ (¬ p124) ∨ (¬ p211) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h25787 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u9)

theorem step27302 (p10 p39 p63 p68 p101 p124 p211 p323 p595 p603 p616 : Prop)
    (h26883 : p616 ∨ p595)
    (h26861 : p323 ∨ p10)
    (h17657 : (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p211) ∨ (¬ p323) ∨ (¬ p603) ∨ (¬ p616)) : p595 ∨ (¬ p101) ∨ (¬ p211) ∨ (¬ p603) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p124) ∨ p10 ∨ (¬ p68) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p595) := fun hu => hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p603 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h17657 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u3)
  · exact False.elim (q8 u9)

theorem step27303 (p8 p10 p101 p308 p323 p348 p710 : Prop)
    (h26889 : p710 ∨ p8)
    (h26861 : p323 ∨ p10)
    (h18347 : (¬ p101) ∨ (¬ p308) ∨ (¬ p323) ∨ (¬ p348) ∨ (¬ p710)) : (¬ p101) ∨ (¬ p308) ∨ p8 ∨ (¬ p348) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p308 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18347 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step27304 (p10 p101 p323 p434 p734 : Prop)
    (h26861 : p323 ∨ p10)
    (h20120 : (¬ p101) ∨ (¬ p323) ∨ (¬ p434) ∨ (¬ p734)) : (¬ p434) ∨ (¬ p734) ∨ (¬ p101) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20120 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)

theorem step27305 (p10 p101 p285 p323 p348 p836 : Prop)
    (h26861 : p323 ∨ p10)
    (h18337 : (¬ p101) ∨ (¬ p285) ∨ (¬ p323) ∨ (¬ p348) ∨ (¬ p836)) : (¬ p836) ∨ (¬ p285) ∨ (¬ p348) ∨ p10 ∨ (¬ p101) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p285 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18337 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)

theorem step27306 (p10 p11 p140 p189 p227 p266 p323 : Prop)
    (h26861 : p323 ∨ p10)
    (h18639 : (¬ p11) ∨ (¬ p140) ∨ (¬ p189) ∨ (¬ p227) ∨ (¬ p266) ∨ (¬ p323)) : (¬ p266) ∨ (¬ p11) ∨ (¬ p189) ∨ (¬ p140) ∨ p10 ∨ (¬ p227) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18639 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u6)

theorem step27309 (p10 p14 p18 p19 p163 p229 p323 : Prop)
    (h26849 : p229 ∨ p14)
    (h26829 : p19 ∨ p18)
    (h26861 : p323 ∨ p10)
    (h19188 : (¬ p19) ∨ (¬ p163) ∨ (¬ p229) ∨ (¬ p323)) : p14 ∨ p18 ∨ (¬ p163) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19188 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)

theorem step27310 (p3 p6 p10 p127 p163 p226 p323 : Prop)
    (h26847 : p226 ∨ p3)
    (h26839 : p127 ∨ p6)
    (h26861 : p323 ∨ p10)
    (h19604 : (¬ p127) ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p323)) : p3 ∨ p6 ∨ (¬ p163) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19604 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)

theorem step27311 (p10 p89 p125 p185 p237 p323 p576 p581 p918 : Prop)
    (h26851 : p237 ∨ p185)
    (h26861 : p323 ∨ p10)
    (h26879 : p581 ∨ p576)
    (h25788 : (¬ p581) ∨ (¬ p237) ∨ (¬ p125) ∨ (¬ p918) ∨ (¬ p89) ∨ (¬ p323)) : p185 ∨ (¬ p918) ∨ p10 ∨ p576 ∨ (¬ p125) ∨ (¬ p89) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25788 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u7)

theorem step27312 (p10 p24 p323 p420 p601 : Prop)
    (h26880 : (¬ p420) ∨ (¬ p601))
    (h26861 : p323 ∨ p10)
    (h14419 : (¬ p24) ∨ (¬ p323) ∨ p601) : (¬ p420) ∨ (¬ p24) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p601) := by
    rcases h26880 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u4 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h14419 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (u3 q2)

theorem step27313 (p10 p101 p323 p420 p495 : Prop)
    (h26861 : p323 ∨ p10)
    (h18721 : (¬ p101) ∨ (¬ p323) ∨ (¬ p420) ∨ (¬ p495)) : (¬ p420) ∨ (¬ p101) ∨ p10 ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18721 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)

theorem step27314 (p10 p15 p24 p69 p303 p323 p387 p495 p499 : Prop)
    (h26875 : p499 ∨ p495)
    (h26867 : p387 ∨ p303)
    (h26861 : p323 ∨ p10)
    (h26833 : p69 ∨ p15)
    (h17895 : (¬ p24) ∨ (¬ p69) ∨ (¬ p323) ∨ (¬ p387) ∨ (¬ p499)) : p495 ∨ p303 ∨ (¬ p24) ∨ p10 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17895 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step27317 (p10 p140 p185 p237 p323 p576 p581 p918 : Prop)
    (h26851 : p237 ∨ p185)
    (h26879 : p581 ∨ p576)
    (h26861 : p323 ∨ p10)
    (h19101 : (¬ p140) ∨ (¬ p237) ∨ (¬ p323) ∨ (¬ p581) ∨ (¬ p918)) : p185 ∨ p576 ∨ (¬ p140) ∨ (¬ p918) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19101 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)

theorem step27318 (p10 p17 p256 p323 p515 p790 p814 : Prop)
    (h26893 : p814 ∨ p790)
    (h26853 : p256 ∨ p17)
    (h26861 : p323 ∨ p10)
    (h22712 : (¬ p515) ∨ (¬ p814) ∨ (¬ p256) ∨ (¬ p323)) : (¬ p515) ∨ p790 ∨ p17 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p515 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p790) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h22712 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)

theorem step27319 (p10 p323 p325 p337 p338 p339 p340 p341 : Prop)
    (h26860 : (¬ p10) ∨ (¬ p323))
    (h1731 : p323 ∨ p325 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : (¬ p341) ∨ (¬ p337) ∨ (¬ p340) ∨ (¬ p338) ∨ p325 ∨ (¬ p10) ∨ (¬ p339) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p341 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p337 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p340 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p338 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p339 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p323) := by
    rcases h26860 with q0 | q1
    · exact False.elim (q0 u5)
    · exact q1
  rcases h1731 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u0)

theorem step27328 (p10 p323 p325 p336 p341 : Prop)
    (h26860 : (¬ p10) ∨ (¬ p323))
    (h21602 : p336 ∨ (¬ p341) ∨ p323 ∨ p325) : p336 ∨ (¬ p341) ∨ p325 ∨ (¬ p10) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p336) := fun hu => hn (Or.inl hu)
  have u1 : p341 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p325) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p323) := by
    rcases h26860 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h21602 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (u4 q2)
  · exact False.elim (u2 q3)

theorem step27329 (p10 p323 p325 p332 p333 p334 p335 p336 : Prop)
    (h26860 : (¬ p10) ∨ (¬ p323))
    (h1706 : p323 ∨ p325 ∨ (¬ p332) ∨ (¬ p333) ∨ (¬ p334) ∨ (¬ p335) ∨ (¬ p336)) : (¬ p332) ∨ (¬ p333) ∨ p325 ∨ (¬ p10) ∨ (¬ p335) ∨ (¬ p336) ∨ (¬ p334) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p332 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p325) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p336 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p323) := by
    rcases h26860 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h1706 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step27330 (p17 p256 p1497 : Prop)
    (h26853 : p256 ∨ p17)
    (h18279 : (¬ p256) ∨ p1497) : p17 ∨ p1497 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p17) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1497) := fun hu => hn (Or.inr hu)
  have u2 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18279 with q0 | q1
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)

theorem step27332 (p17 p126 p185 p237 p256 : Prop)
    (h26850 : (¬ p185) ∨ (¬ p237))
    (h26853 : p256 ∨ p17)
    (h21454 : p237 ∨ (¬ p256) ∨ (¬ p126)) : (¬ p185) ∨ p17 ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p237) := by
    rcases h26850 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u4 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h21454 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)

theorem step27334 (p124 p258 p266 p516 p790 p814 : Prop)
    (h26893 : p814 ∨ p790)
    (h16438 : (¬ p124) ∨ (¬ p258) ∨ (¬ p266) ∨ (¬ p516) ∨ (¬ p814)) : (¬ p516) ∨ (¬ p266) ∨ p790 ∨ (¬ p258) ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p516 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16438 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step27343 (p126 p301 p519 : Prop)
    (h26856 : (¬ p126) ∨ (¬ p301))
    (h24776 : p519 ∨ p301) : p519 ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p519) := fun hu => hn (Or.inl hu)
  have u1 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p301) := by
    rcases h26856 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24776 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step27349 (p17 p136 p189 p256 : Prop)
    (h26853 : p256 ∨ p17)
    (h5964 : (¬ p136) ∨ (¬ p189) ∨ (¬ p256)) : p17 ∨ (¬ p189) ∨ (¬ p136) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p17) := fun hu => hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p136 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5964 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step27355 (p189 p190 p193 p201 p202 p203 p204 p205 : Prop)
    (h26844 : (¬ p189) ∨ (¬ p193))
    (h964 : p190 ∨ p193 ∨ (¬ p201) ∨ (¬ p202) ∨ (¬ p203) ∨ (¬ p204) ∨ (¬ p205)) : (¬ p202) ∨ (¬ p205) ∨ (¬ p189) ∨ p190 ∨ (¬ p203) ∨ (¬ p201) ∨ (¬ p204) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p202 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p205 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p190) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p203 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p201 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p204 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p193) := by
    rcases h26844 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h964 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u1)

theorem step27360 (p3 p185 p188 p189 p193 p237 : Prop)
    (h26851 : p237 ∨ p185)
    (h26844 : (¬ p189) ∨ (¬ p193))
    (h22383 : (¬ p188) ∨ p193 ∨ p3 ∨ (¬ p237)) : p3 ∨ p185 ∨ (¬ p188) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : (¬ p193) := by
    rcases h26844 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h22383 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (u5 q1)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u4)

theorem step27361 (p3 p18 p19 p163 p226 p423 p1140 p1141 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26829 : p19 ∨ p18)
    (h26847 : p226 ∨ p3)
    (h19138 : (¬ p19) ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p1140) ∨ (¬ p1141)) : p423 ∨ (¬ p1140) ∨ p18 ∨ p3 ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19138 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)

theorem step27362 (p3 p163 p226 p419 p424 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26847 : p226 ∨ p3)
    (h18142 : (¬ p163) ∨ (¬ p226) ∨ (¬ p419) ∨ (¬ p796)) : p424 ∨ (¬ p163) ∨ p3 ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18142 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step27363 (p3 p163 p192 p226 : Prop)
    (h26847 : p226 ∨ p3)
    (h12196 : (¬ p163) ∨ (¬ p192) ∨ (¬ p226)) : p3 ∨ (¬ p192) ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h12196 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step27364 (p3 p163 p188 p226 p303 p331 p382 p406 p424 p796 p817 : Prop)
    (h26847 : p226 ∨ p3)
    (h26891 : p796 ∨ p424)
    (h26869 : p406 ∨ p382)
    (h18143 : (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p303) ∨ (¬ p331) ∨ (¬ p406) ∨ (¬ p796) ∨ (¬ p817)) : p3 ∨ p424 ∨ p382 ∨ (¬ p188) ∨ (¬ p817) ∨ (¬ p303) ∨ (¬ p163) ∨ (¬ p331) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p424) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p817 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18143 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u4)

theorem step27365 (p3 p163 p188 p226 p382 p406 p424 p796 p817 p1191 p1287 : Prop)
    (h26847 : p226 ∨ p3)
    (h26869 : p406 ∨ p382)
    (h26891 : p796 ∨ p424)
    (h19522 : (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p406) ∨ (¬ p796) ∨ (¬ p817) ∨ (¬ p1191) ∨ (¬ p1287)) : p3 ∨ p382 ∨ (¬ p188) ∨ (¬ p1287) ∨ (¬ p163) ∨ p424 ∨ (¬ p1191) ∨ (¬ p817) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p424) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p817 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19522 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u3)

theorem step27366 (p3 p10 p126 p136 p163 p226 p301 p323 : Prop)
    (h26847 : p226 ∨ p3)
    (h26857 : p301 ∨ p126)
    (h26861 : p323 ∨ p10)
    (h19795 : (¬ p136) ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p301) ∨ (¬ p323)) : p3 ∨ p126 ∨ (¬ p163) ∨ (¬ p136) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p136 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19795 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)

theorem step27367 (p3 p163 p226 p1035 p1140 : Prop)
    (h26847 : p226 ∨ p3)
    (h19130 : (¬ p163) ∨ (¬ p226) ∨ (¬ p1035) ∨ (¬ p1140)) : (¬ p1035) ∨ (¬ p1140) ∨ p3 ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19130 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)

theorem step27368 (p2 p3 p17 p163 p226 p481 p576 p581 p803 p1385 : Prop)
    (h26847 : p226 ∨ p3)
    (h26879 : p581 ∨ p576)
    (h26873 : p481 ∨ p2)
    (h19282 : (¬ p17) ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p481) ∨ (¬ p581) ∨ (¬ p803) ∨ (¬ p1385)) : p3 ∨ p576 ∨ (¬ p17) ∨ (¬ p1385) ∨ p2 ∨ (¬ p163) ∨ (¬ p803) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p803 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19282 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step27370 (p3 p10 p134 p163 p226 : Prop)
    (h26847 : p226 ∨ p3)
    (h18994 : (¬ p10) ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p226)) : p3 ∨ (¬ p10) ∨ (¬ p163) ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18994 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step27374 (p17 p101 p189 p256 p258 p288 : Prop)
    (h26855 : p288 ∨ p258)
    (h26853 : p256 ∨ p17)
    (h17403 : (¬ p101) ∨ (¬ p189) ∨ (¬ p256) ∨ (¬ p288)) : p258 ∨ (¬ p101) ∨ p17 ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p258) := fun hu => hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17403 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step27375 (p2 p101 p141 p258 p288 p424 p481 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26855 : p288 ∨ p258)
    (h26873 : p481 ∨ p2)
    (h20150 : (¬ p101) ∨ (¬ p141) ∨ (¬ p288) ∨ (¬ p481) ∨ (¬ p796)) : p424 ∨ p258 ∨ (¬ p141) ∨ (¬ p101) ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p258) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20150 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u5)

theorem step27377 (p101 p102 p1080 p1207 p1452 p1465 : Prop)
    (h26837 : p102 ∨ p101)
    (h16342 : (¬ p102) ∨ (¬ p1080) ∨ (¬ p1207) ∨ (¬ p1452) ∨ (¬ p1465)) : (¬ p1452) ∨ (¬ p1207) ∨ (¬ p1080) ∨ p101 ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16342 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)

theorem step27379 (p11 p141 p171 p185 p237 p261 p961 p1443 : Prop)
    (h26851 : p237 ∨ p185)
    (h26935 : p1443 ∨ p11)
    (h20300 : (¬ p141) ∨ (¬ p171) ∨ (¬ p237) ∨ (¬ p261) ∨ (¬ p961) ∨ (¬ p1443)) : (¬ p171) ∨ p185 ∨ (¬ p961) ∨ (¬ p261) ∨ p11 ∨ (¬ p141) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20300 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)

theorem step27380 (p11 p18 p141 p210 p961 p1443 : Prop)
    (h26935 : p1443 ∨ p11)
    (h25789 : (¬ p961) ∨ (¬ p1443) ∨ (¬ p210) ∨ (¬ p18) ∨ (¬ p141)) : (¬ p210) ∨ (¬ p961) ∨ (¬ p141) ∨ (¬ p18) ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25789 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)

theorem step27381 (p11 p258 p344 p346 p961 p1443 : Prop)
    (h26935 : p1443 ∨ p11)
    (h26863 : p346 ∨ p344)
    (h20503 : (¬ p258) ∨ (¬ p346) ∨ (¬ p961) ∨ (¬ p1443)) : (¬ p961) ∨ (¬ p258) ∨ p11 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20503 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step27382 (p101 p121 p125 p350 p362 p961 : Prop)
    (h26865 : p362 ∨ p125)
    (h19741 : (¬ p101) ∨ (¬ p121) ∨ (¬ p350) ∨ (¬ p362) ∨ (¬ p961)) : (¬ p961) ∨ (¬ p101) ∨ (¬ p121) ∨ p125 ∨ (¬ p350) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19741 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step27383 (p258 p265 p288 p532 p961 p980 p983 : Prop)
    (h26903 : p983 ∨ p980)
    (h26855 : p288 ∨ p258)
    (h17019 : (¬ p265) ∨ (¬ p288) ∨ (¬ p532) ∨ (¬ p961) ∨ (¬ p983)) : p980 ∨ (¬ p961) ∨ (¬ p532) ∨ (¬ p265) ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17019 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)

theorem step27384 (p41 p45 p101 p121 p192 p206 p961 : Prop)
    (h26831 : p45 ∨ p41)
    (h17234 : (¬ p45) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p192) ∨ (¬ p206) ∨ (¬ p961)) : (¬ p192) ∨ p41 ∨ (¬ p101) ∨ (¬ p206) ∨ (¬ p121) ∨ (¬ p961) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17234 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)

theorem step27385 (p101 p121 p206 p344 p346 p961 : Prop)
    (h26863 : p346 ∨ p344)
    (h19729 : (¬ p101) ∨ (¬ p121) ∨ (¬ p206) ∨ (¬ p346) ∨ (¬ p961)) : (¬ p961) ∨ (¬ p101) ∨ p344 ∨ (¬ p121) ∨ (¬ p206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19729 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step27386 (p11 p206 p283 p344 p836 p961 p1443 : Prop)
    (h26935 : p1443 ∨ p11)
    (h19783 : (¬ p206) ∨ (¬ p283) ∨ (¬ p344) ∨ (¬ p836) ∨ (¬ p961) ∨ (¬ p1443)) : (¬ p961) ∨ (¬ p836) ∨ (¬ p206) ∨ (¬ p283) ∨ (¬ p344) ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19783 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u6)

theorem step27387 (p101 p102 p121 p1083 : Prop)
    (h26837 : p102 ∨ p101)
    (h10265 : (¬ p102) ∨ p121 ∨ (¬ p1083)) : (¬ p1083) ∨ p121 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1083 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h10265 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u0)

theorem step27388 (p187 p422 p1140 p1159 : Prop)
    (h26918 : (¬ p1140) ∨ (¬ p1159))
    (h16081 : (¬ p187) ∨ (¬ p422) ∨ p1159) : (¬ p1140) ∨ (¬ p422) ∨ (¬ p187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1159) := by
    rcases h26918 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h16081 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (u3 q2)

theorem step27389 (p3 p226 p1037 p1140 p1159 : Prop)
    (h26918 : (¬ p1140) ∨ (¬ p1159))
    (h26847 : p226 ∨ p3)
    (h10778 : (¬ p226) ∨ (¬ p1037) ∨ p1159) : (¬ p1037) ∨ (¬ p1140) ∨ p3 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1037 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p3) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1159) := by
    rcases h26918 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u4 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h10778 with q0 | q1 | q2
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (u3 q2)

theorem step27390 (p6 p1140 p1159 p1207 : Prop)
    (h26918 : (¬ p1140) ∨ (¬ p1159))
    (h14946 : (¬ p6) ∨ p1159 ∨ (¬ p1207)) : (¬ p1207) ∨ (¬ p1140) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1159) := by
    rcases h26918 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h14946 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u0)

theorem step27392 (p101 p102 p124 p206 p304 p1140 p1213 : Prop)
    (h26859 : p304 ∨ p124)
    (h26837 : p102 ∨ p101)
    (h16631 : (¬ p102) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p1140) ∨ (¬ p1213)) : p124 ∨ p101 ∨ (¬ p206) ∨ (¬ p1140) ∨ (¬ p1213) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16631 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)

theorem step27393 (p6 p11 p17 p101 p156 p185 p192 p256 p1084 p1443 : Prop)
    (h26935 : p1443 ∨ p11)
    (h26853 : p256 ∨ p17)
    (h18367 : (¬ p6) ∨ (¬ p101) ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p192) ∨ (¬ p256) ∨ (¬ p1084) ∨ (¬ p1443)) : (¬ p185) ∨ p11 ∨ (¬ p156) ∨ (¬ p192) ∨ (¬ p1084) ∨ (¬ p6) ∨ p17 ∨ (¬ p101) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p11) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18367 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u8)

theorem step27394 (p3 p6 p108 p226 : Prop)
    (h26847 : p226 ∨ p3)
    (h12545 : p6 ∨ (¬ p108) ∨ (¬ p226)) : p3 ∨ p6 ∨ (¬ p108) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h12545 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step27400 (p121 p1206 p1211 p1223 : Prop)
    (h26922 : (¬ p121) ∨ (¬ p1206))
    (h21624 : p1223 ∨ p1211 ∨ p1206) : p1223 ∨ p1211 ∨ (¬ p121) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1223) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1211) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1206) := by
    rcases h26922 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h21624 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (u3 q2)

theorem step27401 (p121 p1206 p1211 p1215 p1216 p1217 p1218 p1219 : Prop)
    (h26922 : (¬ p121) ∨ (¬ p1206))
    (h7208 : p1206 ∨ p1211 ∨ (¬ p1215) ∨ (¬ p1216) ∨ (¬ p1217) ∨ (¬ p1218) ∨ (¬ p1219)) : (¬ p1215) ∨ (¬ p1216) ∨ p1211 ∨ (¬ p121) ∨ (¬ p1219) ∨ (¬ p1218) ∨ (¬ p1217) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1215 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1216 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1211) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1219 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1218 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1217 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p1206) := by
    rcases h26922 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h7208 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u4)

theorem step27405 (p121 p1206 p1211 p1220 p1221 p1222 p1223 p1224 : Prop)
    (h26922 : (¬ p121) ∨ (¬ p1206))
    (h7233 : p1206 ∨ p1211 ∨ (¬ p1220) ∨ (¬ p1221) ∨ (¬ p1222) ∨ (¬ p1223) ∨ (¬ p1224)) : (¬ p1224) ∨ (¬ p1220) ∨ p1211 ∨ (¬ p121) ∨ (¬ p1222) ∨ (¬ p1221) ∨ (¬ p1223) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1220 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1211) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1222 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1221 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1223 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p1206) := by
    rcases h26922 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h7233 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u0)

theorem step27409 (p125 p227 p362 p386 : Prop)
    (h26865 : p362 ∨ p125)
    (h14431 : p227 ∨ (¬ p362) ∨ (¬ p386)) : p227 ∨ (¬ p386) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p227) := fun hu => hn (Or.inl hu)
  have u1 : p386 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h14431 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)

theorem step27410 (p124 p304 p312 : Prop)
    (h26859 : p304 ∨ p124)
    (h21015 : (¬ p304) ∨ p312) : p124 ∨ p312 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p312) := fun hu => hn (Or.inr hu)
  have u2 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h21015 with q0 | q1
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)

theorem step27411 (p124 p304 p642 : Prop)
    (h26859 : p304 ∨ p124)
    (h17709 : (¬ p304) ∨ p642) : p124 ∨ p642 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p642) := fun hu => hn (Or.inr hu)
  have u2 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17709 with q0 | q1
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)

theorem step27412 (p124 p227 p258 p288 p304 p1452 : Prop)
    (h26859 : p304 ∨ p124)
    (h26855 : p288 ∨ p258)
    (h18440 : (¬ p227) ∨ (¬ p288) ∨ (¬ p304) ∨ (¬ p1452)) : p124 ∨ p258 ∨ (¬ p1452) ∨ (¬ p227) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p258) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18440 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step27413 (p124 p258 p261 p288 p304 p790 p1385 : Prop)
    (h26859 : p304 ∨ p124)
    (h26855 : p288 ∨ p258)
    (h19178 : (¬ p261) ∨ (¬ p288) ∨ (¬ p304) ∨ (¬ p790) ∨ (¬ p1385)) : (¬ p790) ∨ (¬ p261) ∨ p124 ∨ p258 ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19178 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)

theorem step27414 (p124 p125 p258 p288 p303 p304 p362 p387 : Prop)
    (h26867 : p387 ∨ p303)
    (h26859 : p304 ∨ p124)
    (h26855 : p288 ∨ p258)
    (h26865 : p362 ∨ p125)
    (h18442 : (¬ p288) ∨ (¬ p304) ∨ (¬ p362) ∨ (¬ p387)) : p303 ∨ p124 ∨ p258 ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18442 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)

theorem step27415 (p124 p125 p258 p288 p304 p362 p434 : Prop)
    (h26859 : p304 ∨ p124)
    (h26855 : p288 ∨ p258)
    (h26865 : p362 ∨ p125)
    (h18448 : (¬ p288) ∨ (¬ p304) ∨ (¬ p362) ∨ (¬ p434)) : p124 ∨ (¬ p434) ∨ p258 ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18448 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)

theorem step27416 (p124 p258 p265 p304 : Prop)
    (h26859 : p304 ∨ p124)
    (h10858 : p258 ∨ (¬ p265) ∨ (¬ p304)) : p124 ∨ (¬ p265) ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h10858 with q0 | q1 | q2
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step27417 (p124 p126 p265 p304 p345 : Prop)
    (h26859 : p304 ∨ p124)
    (h10575 : (¬ p126) ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p345)) : p124 ∨ (¬ p265) ∨ (¬ p126) ∨ (¬ p345) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h10575 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)

theorem step27419 (p11 p124 p258 p288 p304 p389 p595 p1286 : Prop)
    (h26859 : p304 ∨ p124)
    (h26855 : p288 ∨ p258)
    (h25790 : (¬ p389) ∨ (¬ p304) ∨ (¬ p288) ∨ (¬ p595) ∨ (¬ p1286) ∨ (¬ p11)) : (¬ p389) ∨ (¬ p11) ∨ p124 ∨ p258 ∨ (¬ p1286) ∨ (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25790 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u1)

theorem step27420 (p124 p126 p258 p261 p288 p301 p304 p327 p382 p406 p419 p817 : Prop)
    (h26857 : p301 ∨ p126)
    (h26859 : p304 ∨ p124)
    (h26869 : p406 ∨ p382)
    (h26855 : p288 ∨ p258)
    (h17745 : (¬ p261) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p304) ∨ (¬ p327) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p817)) : p126 ∨ (¬ p327) ∨ (¬ p261) ∨ (¬ p419) ∨ (¬ p817) ∨ p124 ∨ p382 ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p817 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h17745 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step27421 (p124 p126 p258 p261 p288 p301 p304 p327 p435 p687 p817 : Prop)
    (h26859 : p304 ∨ p124)
    (h26857 : p301 ∨ p126)
    (h26855 : p288 ∨ p258)
    (h20459 : (¬ p261) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p304) ∨ (¬ p327) ∨ (¬ p435) ∨ (¬ p687) ∨ (¬ p817)) : p124 ∨ p126 ∨ (¬ p435) ∨ (¬ p687) ∨ (¬ p261) ∨ (¬ p327) ∨ (¬ p817) ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p817 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20459 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u6)

theorem step27422 (p124 p125 p258 p288 p304 p331 p362 p419 p789 p790 p814 p858 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26859 : p304 ∨ p124)
    (h26893 : p814 ∨ p790)
    (h26865 : p362 ∨ p125)
    (h26855 : p288 ∨ p258)
    (h26897 : p858 ∨ p789)
    (h18449 : (¬ p288) ∨ (¬ p304) ∨ (¬ p331) ∨ (¬ p362) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p996)) : p419 ∨ p124 ∨ p790 ∨ p125 ∨ p258 ∨ (¬ p331) ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u12 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18449 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u11)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u7)

theorem step27423 (p124 p135 p185 p189 p237 p265 p304 p344 p346 p668 p1115 p1116 : Prop)
    (h26859 : p304 ∨ p124)
    (h26851 : p237 ∨ p185)
    (h26863 : p346 ∨ p344)
    (h26915 : p1116 ∨ p1115)
    (h20434 : (¬ p135) ∨ (¬ p189) ∨ (¬ p237) ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p668) ∨ (¬ p1116)) : p124 ∨ (¬ p265) ∨ p185 ∨ (¬ p135) ∨ p344 ∨ p1115 ∨ (¬ p189) ∨ (¬ p668) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20434 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u11)

theorem step27425 (p11 p124 p160 p258 p261 p288 p304 p389 p1325 p1350 : Prop)
    (h26859 : p304 ∨ p124)
    (h26855 : p288 ∨ p258)
    (h19010 : (¬ p11) ∨ (¬ p160) ∨ (¬ p261) ∨ (¬ p288) ∨ (¬ p304) ∨ (¬ p389) ∨ (¬ p1325) ∨ (¬ p1350)) : (¬ p160) ∨ (¬ p11) ∨ (¬ p1325) ∨ p124 ∨ (¬ p389) ∨ p258 ∨ (¬ p1350) ∨ (¬ p261) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19010 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u6)

theorem step27426 (p124 p141 p210 p258 p288 p304 p326 p424 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26859 : p304 ∨ p124)
    (h26855 : p288 ∨ p258)
    (h20500 : (¬ p141) ∨ (¬ p210) ∨ (¬ p288) ∨ (¬ p304) ∨ (¬ p326) ∨ (¬ p796)) : p424 ∨ p124 ∨ p258 ∨ (¬ p210) ∨ (¬ p326) ∨ (¬ p141) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20500 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)

theorem step27427 (p18 p124 p141 p210 p258 p288 p304 : Prop)
    (h26859 : p304 ∨ p124)
    (h26855 : p288 ∨ p258)
    (h25791 : (¬ p304) ∨ (¬ p210) ∨ (¬ p141) ∨ (¬ p18) ∨ (¬ p288)) : (¬ p210) ∨ p124 ∨ (¬ p18) ∨ p258 ∨ (¬ p141) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25791 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)

theorem step27428 (p11 p17 p185 p237 p286 p1080 : Prop)
    (h26851 : p237 ∨ p185)
    (h20299 : (¬ p11) ∨ (¬ p17) ∨ (¬ p237) ∨ (¬ p286) ∨ (¬ p1080)) : (¬ p11) ∨ (¬ p1080) ∨ (¬ p17) ∨ (¬ p286) ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20299 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)

theorem step27429 (p11 p15 p17 p39 p69 p88 p389 p419 p595 p996 p1192 : Prop)
    (h26833 : p69 ∨ p15)
    (h26905 : p996 ∨ p419)
    (h20445 : (¬ p11) ∨ (¬ p17) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p389) ∨ (¬ p595) ∨ (¬ p996) ∨ (¬ p1192)) : (¬ p389) ∨ (¬ p11) ∨ (¬ p595) ∨ (¬ p17) ∨ (¬ p88) ∨ p15 ∨ (¬ p1192) ∨ (¬ p39) ∨ p419 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h20445 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u6)

theorem step27430 (p2 p11 p17 p39 p68 p88 p481 p532 p1330 p1366 : Prop)
    (h26873 : p481 ∨ p2)
    (h20453 : (¬ p11) ∨ (¬ p17) ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p481) ∨ (¬ p532) ∨ (¬ p1330) ∨ (¬ p1366)) : (¬ p1366) ∨ (¬ p11) ∨ (¬ p39) ∨ (¬ p17) ∨ (¬ p88) ∨ p2 ∨ (¬ p68) ∨ (¬ p1330) ∨ (¬ p532) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20453 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u0)

theorem step27431 (p3 p11 p17 p190 p224 p225 p389 p544 p657 : Prop)
    (h26877 : p544 ∨ p225)
    (h26887 : p657 ∨ p224)
    (h20487 : (¬ p3) ∨ (¬ p11) ∨ (¬ p17) ∨ (¬ p190) ∨ (¬ p389) ∨ (¬ p544) ∨ (¬ p657)) : (¬ p389) ∨ (¬ p11) ∨ (¬ p17) ∨ (¬ p190) ∨ p225 ∨ p224 ∨ (¬ p3) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u8 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20487 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)

theorem step27432 (p11 p160 p258 p288 p532 p1353 : Prop)
    (h26855 : p288 ∨ p258)
    (h16446 : (¬ p11) ∨ (¬ p160) ∨ (¬ p288) ∨ (¬ p532) ∨ (¬ p1353)) : (¬ p160) ∨ (¬ p1353) ∨ (¬ p532) ∨ p258 ∨ (¬ p11) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1353 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16446 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u1)

theorem step27433 (p11 p125 p227 p258 p288 : Prop)
    (h26855 : p288 ∨ p258)
    (h16448 : (¬ p11) ∨ (¬ p125) ∨ (¬ p227) ∨ (¬ p288)) : (¬ p227) ∨ (¬ p11) ∨ (¬ p125) ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16448 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step27435 (p11 p258 p288 p642 p1079 p1095 : Prop)
    (h26855 : p288 ∨ p258)
    (h17121 : (¬ p11) ∨ (¬ p288) ∨ (¬ p642) ∨ (¬ p1079) ∨ (¬ p1095)) : (¬ p11) ∨ (¬ p1095) ∨ p258 ∨ (¬ p1079) ∨ (¬ p642) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1079 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p642 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17121 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)

theorem step27436 (p11 p227 p258 p266 p288 p756 : Prop)
    (h26855 : p288 ∨ p258)
    (h18205 : (¬ p11) ∨ (¬ p227) ∨ (¬ p266) ∨ (¬ p288) ∨ (¬ p756)) : (¬ p756) ∨ (¬ p11) ∨ p258 ∨ (¬ p266) ∨ (¬ p227) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18205 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step27437 (p11 p18 p19 p207 p227 p258 p288 : Prop)
    (h26855 : p288 ∨ p258)
    (h26829 : p19 ∨ p18)
    (h18884 : (¬ p11) ∨ (¬ p19) ∨ (¬ p207) ∨ (¬ p227) ∨ (¬ p288)) : (¬ p11) ∨ (¬ p227) ∨ p258 ∨ p18 ∨ (¬ p207) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18884 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)

theorem step27439 (p11 p12 p125 p126 p239 p261 p534 p1036 p1055 p1061 : Prop)
    (h26907 : p1036 ∨ p12)
    (h26909 : p1061 ∨ p1055)
    (h19151 : (¬ p11) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p239) ∨ (¬ p261) ∨ (¬ p534) ∨ (¬ p1036) ∨ (¬ p1061)) : (¬ p534) ∨ (¬ p125) ∨ (¬ p261) ∨ (¬ p126) ∨ (¬ p239) ∨ p12 ∨ (¬ p11) ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p239 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u9 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19151 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u9)

theorem step27440 (p11 p125 p126 p225 p239 p261 p536 p544 p940 : Prop)
    (h26877 : p544 ∨ p225)
    (h19153 : (¬ p11) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p239) ∨ (¬ p261) ∨ (¬ p536) ∨ (¬ p544) ∨ (¬ p940)) : (¬ p940) ∨ (¬ p11) ∨ (¬ p239) ∨ (¬ p536) ∨ (¬ p126) ∨ (¬ p125) ∨ p225 ∨ (¬ p261) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p239 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19153 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u0)

theorem step27441 (p11 p227 p258 p288 p344 : Prop)
    (h26855 : p288 ∨ p258)
    (h16590 : (¬ p11) ∨ (¬ p227) ∨ (¬ p288) ∨ (¬ p344)) : (¬ p11) ∨ (¬ p227) ∨ p258 ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16590 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)

theorem step27442 (p11 p41 p45 p89 p189 p193 p532 p1000 p1255 p1273 p1325 p1333 : Prop)
    (h26831 : p45 ∨ p41)
    (h26845 : p193 ∨ p189)
    (h26931 : p1333 ∨ p1325)
    (h19105 : (¬ p11) ∨ (¬ p45) ∨ (¬ p89) ∨ (¬ p193) ∨ (¬ p532) ∨ (¬ p1000) ∨ (¬ p1255) ∨ (¬ p1273) ∨ (¬ p1333)) : (¬ p1273) ∨ (¬ p1255) ∨ (¬ p89) ∨ p41 ∨ (¬ p11) ∨ (¬ p1000) ∨ p189 ∨ p1325 ∨ (¬ p532) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19105 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u11)

theorem step27443 (p11 p124 p126 p227 p304 p350 : Prop)
    (h26859 : p304 ∨ p124)
    (h16494 : (¬ p11) ∨ (¬ p126) ∨ (¬ p227) ∨ (¬ p304) ∨ (¬ p350)) : (¬ p227) ∨ (¬ p11) ∨ (¬ p126) ∨ p124 ∨ (¬ p350) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16494 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)

theorem step27458 (p124 p125 p304 p362 p434 p734 : Prop)
    (h26859 : p304 ∨ p124)
    (h26865 : p362 ∨ p125)
    (h18498 : (¬ p304) ∨ (¬ p362) ∨ (¬ p434) ∨ (¬ p734)) : (¬ p434) ∨ p124 ∨ p125 ∨ (¬ p734) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18498 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)

theorem step27459 (p124 p258 p265 p288 : Prop)
    (h26855 : p288 ∨ p258)
    (h11982 : p124 ∨ (¬ p265) ∨ (¬ p288)) : (¬ p265) ∨ p258 ∨ p124 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p258) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p124) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h11982 with q0 | q1 | q2
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)

theorem step27460 (p224 p657 p664 : Prop)
    (h26887 : p657 ∨ p224)
    (h21023 : (¬ p657) ∨ p664) : p224 ∨ p664 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p224) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p664) := fun hu => hn (Or.inr hu)
  have u2 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h21023 with q0 | q1
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)

theorem step27462 (p224 p303 p348 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h11604 : (¬ p303) ∨ (¬ p348) ∨ (¬ p657)) : (¬ p348) ∨ p224 ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h11604 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)

theorem step27464 (p126 p224 p258 p288 p301 p303 p657 : Prop)
    (h26857 : p301 ∨ p126)
    (h26855 : p288 ∨ p258)
    (h26887 : p657 ∨ p224)
    (h17028 : (¬ p288) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p657)) : p126 ∨ (¬ p303) ∨ p258 ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17028 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)

theorem step27466 (p224 p290 p303 p345 p657 p836 p840 : Prop)
    (h26887 : p657 ∨ p224)
    (h26895 : p840 ∨ p836)
    (h17915 : (¬ p290) ∨ (¬ p303) ∨ (¬ p345) ∨ (¬ p657) ∨ (¬ p840)) : (¬ p290) ∨ p224 ∨ (¬ p303) ∨ (¬ p345) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p290 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17915 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step27467 (p224 p303 p420 p495 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h20082 : (¬ p303) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p657)) : (¬ p420) ∨ p224 ∨ (¬ p303) ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20082 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step27469 (p124 p125 p224 p303 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h18662 : (¬ p124) ∨ (¬ p125) ∨ (¬ p303) ∨ (¬ p657)) : (¬ p125) ∨ (¬ p124) ∨ p224 ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18662 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step27470 (p224 p303 p420 p633 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h17891 : (¬ p303) ∨ (¬ p420) ∨ (¬ p633) ∨ (¬ p657)) : (¬ p420) ∨ p224 ∨ (¬ p303) ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17891 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step27471 (p101 p102 p224 p349 p434 p657 p734 : Prop)
    (h26837 : p102 ∨ p101)
    (h26887 : p657 ∨ p224)
    (h19722 : (¬ p102) ∨ (¬ p349) ∨ (¬ p434) ∨ (¬ p657) ∨ (¬ p734)) : (¬ p434) ∨ (¬ p734) ∨ (¬ p349) ∨ p101 ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19722 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)

theorem step27473 (p224 p382 p406 p657 p713 : Prop)
    (h26887 : p657 ∨ p224)
    (h26868 : (¬ p382) ∨ (¬ p406))
    (h10666 : p406 ∨ (¬ p657) ∨ (¬ p713)) : (¬ p713) ∨ p224 ∨ (¬ p382) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p713 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u4 : (¬ p406) := by
    rcases h26868 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h10666 with q0 | q1 | q2
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)

theorem step27475 (p125 p224 p362 p434 p657 p734 : Prop)
    (h26887 : p657 ∨ p224)
    (h26865 : p362 ∨ p125)
    (h19505 : (¬ p362) ∨ (¬ p434) ∨ (¬ p657) ∨ (¬ p734)) : (¬ p734) ∨ (¬ p434) ∨ p224 ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19505 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step27476 (p224 p382 p536 p657 p709 p738 : Prop)
    (h26887 : p657 ∨ p224)
    (h16695 : (¬ p382) ∨ (¬ p536) ∨ (¬ p657) ∨ (¬ p709) ∨ (¬ p738)) : (¬ p536) ∨ (¬ p738) ∨ (¬ p382) ∨ (¬ p709) ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p738 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16695 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)

theorem step27477 (p18 p19 p224 p234 p382 p480 p657 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26829 : p19 ∨ p18)
    (h26887 : p657 ∨ p224)
    (h20094 : (¬ p19) ∨ (¬ p382) ∨ (¬ p480) ∨ (¬ p657) ∨ (¬ p1187)) : p234 ∨ p18 ∨ (¬ p382) ∨ (¬ p480) ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p480 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20094 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u5)

theorem step27478 (p17 p83 p344 p576 p581 p897 p922 : Prop)
    (h26879 : p581 ∨ p576)
    (h17068 : (¬ p17) ∨ (¬ p83) ∨ (¬ p344) ∨ (¬ p581) ∨ (¬ p897) ∨ (¬ p922)) : (¬ p344) ∨ (¬ p897) ∨ (¬ p83) ∨ (¬ p17) ∨ (¬ p922) ∨ p576 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p922 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17068 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u4)

theorem step27479 (p17 p83 p344 p576 p581 p835 p1385 : Prop)
    (h26879 : p581 ∨ p576)
    (h19843 : (¬ p17) ∨ (¬ p83) ∨ (¬ p344) ∨ (¬ p581) ∨ (¬ p835) ∨ (¬ p1385)) : (¬ p1385) ∨ p576 ∨ (¬ p17) ∨ (¬ p835) ∨ (¬ p344) ∨ (¬ p83) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p835 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19843 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u0)

theorem step27480 (p17 p189 p256 p258 p288 p344 : Prop)
    (h26853 : p256 ∨ p17)
    (h26855 : p288 ∨ p258)
    (h17185 : (¬ p189) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p344)) : (¬ p344) ∨ p17 ∨ (¬ p189) ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17185 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)

theorem step27481 (p124 p125 p224 p344 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h19680 : (¬ p124) ∨ (¬ p125) ∨ (¬ p344) ∨ (¬ p657)) : (¬ p125) ∨ p224 ∨ (¬ p124) ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19680 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step27482 (p17 p224 p256 p258 p288 p344 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h26853 : p256 ∨ p17)
    (h26855 : p288 ∨ p258)
    (h16985 : (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p657)) : (¬ p344) ∨ p224 ∨ p17 ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16985 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step27483 (p17 p256 p258 p288 p344 p728 : Prop)
    (h26853 : p256 ∨ p17)
    (h26855 : p288 ∨ p258)
    (h16464 : (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p728)) : (¬ p728) ∨ (¬ p344) ∨ p17 ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16464 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)

theorem step27484 (p3 p225 p226 p344 p1076 : Prop)
    (h26847 : p226 ∨ p3)
    (h16390 : (¬ p225) ∨ (¬ p226) ∨ (¬ p344) ∨ (¬ p1076)) : p3 ∨ (¬ p344) ∨ (¬ p225) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16390 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)

theorem step27485 (p8 p17 p90 p224 p228 p241 p256 p455 p574 p710 p918 : Prop)
    (h26853 : p256 ∨ p17)
    (h26586 : p90)
    (h26889 : p710 ∨ p8)
    (h18668 : (¬ p90) ∨ (¬ p224) ∨ (¬ p228) ∨ (¬ p241) ∨ (¬ p256) ∨ (¬ p455) ∨ (¬ p574) ∨ (¬ p710) ∨ (¬ p918)) : (¬ p241) ∨ p17 ∨ (¬ p455) ∨ (¬ p224) ∨ (¬ p228) ∨ (¬ p918) ∨ p8 ∨ (¬ p574) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p574 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p90 := by
    exact h26586
  have u10 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18668 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u5)

theorem step27486 (p11 p455 p456 p574 : Prop)
    (h26870 : (¬ p455) ∨ (¬ p456))
    (h13923 : (¬ p11) ∨ p456 ∨ (¬ p574)) : (¬ p455) ∨ (¬ p11) ∨ (¬ p574) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p574 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p456) := by
    rcases h26870 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h13923 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u2)

theorem step27487 (p126 p301 p420 p574 p601 : Prop)
    (h26857 : p301 ∨ p126)
    (h26881 : p601 ∨ p420)
    (h14083 : (¬ p301) ∨ (¬ p574) ∨ (¬ p601)) : p126 ∨ (¬ p574) ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p574 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h14083 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)

theorem step27488 (p63 p126 p301 p303 p495 p574 : Prop)
    (h26857 : p301 ∨ p126)
    (h20022 : (¬ p63) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p495) ∨ (¬ p574)) : (¬ p63) ∨ (¬ p495) ∨ (¬ p303) ∨ (¬ p574) ∨ p126 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p574 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p126) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20022 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)

theorem step27491 (p17 p90 p256 p344 p574 p633 p727 p918 p1584 : Prop)
    (h26586 : p90)
    (h26853 : p256 ∨ p17)
    (h18221 : (¬ p90) ∨ (¬ p256) ∨ (¬ p344) ∨ (¬ p574) ∨ (¬ p633) ∨ (¬ p727) ∨ (¬ p918) ∨ (¬ p1584)) : (¬ p1584) ∨ (¬ p727) ∨ (¬ p633) ∨ (¬ p344) ∨ p17 ∨ (¬ p574) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p727 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p574 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p90 := by
    exact h26586
  have u8 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18221 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u0)

theorem step27492 (p17 p90 p241 p256 p344 p574 p633 p664 p918 p1055 : Prop)
    (h26586 : p90)
    (h26853 : p256 ∨ p17)
    (h18226 : (¬ p90) ∨ (¬ p241) ∨ (¬ p256) ∨ (¬ p344) ∨ (¬ p574) ∨ (¬ p633) ∨ (¬ p664) ∨ (¬ p918) ∨ (¬ p1055)) : (¬ p241) ∨ (¬ p1055) ∨ (¬ p574) ∨ (¬ p664) ∨ (¬ p633) ∨ (¬ p344) ∨ p17 ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p574 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p90 := by
    exact h26586
  have u9 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18226 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u1)

theorem step27494 (p668 p836 p840 : Prop)
    (h26895 : p840 ∨ p836)
    (h20545 : p668 ∨ (¬ p840)) : p668 ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p668) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p836) := fun hu => hn (Or.inr hu)
  have u2 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20545 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)

theorem step27495 (p737 p836 p840 p1584 : Prop)
    (h26895 : p840 ∨ p836)
    (h10634 : (¬ p737) ∨ (¬ p840) ∨ (¬ p1584)) : (¬ p1584) ∨ (¬ p737) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p737 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h10634 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)

theorem step27496 (p63 p344 p346 p836 p840 p918 p928 : Prop)
    (h26901 : p928 ∨ p918)
    (h26863 : p346 ∨ p344)
    (h26895 : p840 ∨ p836)
    (h18549 : (¬ p63) ∨ (¬ p346) ∨ (¬ p840) ∨ (¬ p928)) : p918 ∨ p344 ∨ p836 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p918) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18549 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)

theorem step27497 (p41 p45 p224 p657 p836 p840 p918 p928 : Prop)
    (h26901 : p928 ∨ p918)
    (h26831 : p45 ∨ p41)
    (h26887 : p657 ∨ p224)
    (h26895 : p840 ∨ p836)
    (h16252 : (¬ p45) ∨ (¬ p657) ∨ (¬ p840) ∨ (¬ p928)) : p918 ∨ p41 ∨ p224 ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p918) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16252 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)

theorem step27498 (p41 p45 p189 p193 p836 p840 p918 p928 : Prop)
    (h26901 : p928 ∨ p918)
    (h26831 : p45 ∨ p41)
    (h26895 : p840 ∨ p836)
    (h26845 : p193 ∨ p189)
    (h17358 : (¬ p45) ∨ (¬ p193) ∨ (¬ p840) ∨ (¬ p928)) : p918 ∨ p41 ∨ p836 ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p918) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17358 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)

theorem step27499 (p41 p45 p225 p836 p840 p918 p928 : Prop)
    (h26901 : p928 ∨ p918)
    (h26831 : p45 ∨ p41)
    (h26895 : p840 ∨ p836)
    (h19355 : (¬ p45) ∨ (¬ p225) ∨ (¬ p840) ∨ (¬ p928)) : p918 ∨ p41 ∨ (¬ p225) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p918) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19355 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)

theorem step27501 (p17 p256 p287 p344 p346 p836 p840 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26863 : p346 ∨ p344)
    (h26895 : p840 ∨ p836)
    (h26853 : p256 ∨ p17)
    (h16501 : (¬ p256) ∨ (¬ p287) ∨ (¬ p346) ∨ (¬ p840) ∨ (¬ p1077)) : p1076 ∨ p344 ∨ (¬ p287) ∨ p836 ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16501 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u5)

theorem step27502 (p303 p420 p495 p836 p840 p1055 p1061 p1115 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26895 : p840 ∨ p836)
    (h22714 : (¬ p1115) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p840) ∨ (¬ p303) ∨ (¬ p1061)) : (¬ p1115) ∨ (¬ p420) ∨ (¬ p303) ∨ p1055 ∨ (¬ p495) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h22714 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)

theorem step27503 (p185 p189 p237 p344 p346 p836 p840 : Prop)
    (h26851 : p237 ∨ p185)
    (h26863 : p346 ∨ p344)
    (h26895 : p840 ∨ p836)
    (h18656 : (¬ p189) ∨ (¬ p237) ∨ (¬ p346) ∨ (¬ p840)) : p185 ∨ p344 ∨ (¬ p189) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18656 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)

theorem step27504 (p185 p189 p225 p237 p836 p840 : Prop)
    (h26851 : p237 ∨ p185)
    (h26895 : p840 ∨ p836)
    (h20050 : (¬ p189) ∨ (¬ p225) ∨ (¬ p237) ∨ (¬ p840)) : p185 ∨ (¬ p225) ∨ (¬ p189) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20050 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step27505 (p255 p344 p346 p836 p840 : Prop)
    (h26863 : p346 ∨ p344)
    (h26895 : p840 ∨ p836)
    (h10292 : (¬ p255) ∨ (¬ p346) ∨ (¬ p840)) : (¬ p255) ∨ p344 ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u4 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h10292 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)

theorem step27507 (p166 p225 p836 p840 : Prop)
    (h26895 : p840 ∨ p836)
    (h13071 : (¬ p166) ∨ (¬ p225) ∨ (¬ p840)) : (¬ p166) ∨ (¬ p225) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p166 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h13071 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step27508 (p4 p10 p101 p102 p290 p836 p840 : Prop)
    (h26895 : p840 ∨ p836)
    (h26837 : p102 ∨ p101)
    (h19649 : (¬ p4) ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p290) ∨ (¬ p840)) : (¬ p10) ∨ (¬ p4) ∨ p836 ∨ (¬ p290) ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p290 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19649 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step27509 (p3 p71 p534 p836 p840 p1584 : Prop)
    (h26895 : p840 ∨ p836)
    (h17704 : (¬ p3) ∨ (¬ p71) ∨ (¬ p534) ∨ (¬ p840) ∨ (¬ p1584)) : (¬ p534) ∨ (¬ p1584) ∨ (¬ p3) ∨ (¬ p71) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17704 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)

theorem step27510 (p185 p224 p237 p657 p836 p840 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26851 : p237 ∨ p185)
    (h26887 : p657 ∨ p224)
    (h26895 : p840 ∨ p836)
    (h17013 : (¬ p237) ∨ (¬ p657) ∨ (¬ p840) ∨ (¬ p1333)) : p1325 ∨ p185 ∨ p224 ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17013 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)

theorem step27511 (p17 p185 p237 p576 p581 p836 p840 : Prop)
    (h26879 : p581 ∨ p576)
    (h26851 : p237 ∨ p185)
    (h26895 : p840 ∨ p836)
    (h17127 : (¬ p17) ∨ (¬ p237) ∨ (¬ p581) ∨ (¬ p840)) : p576 ∨ p185 ∨ p836 ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17127 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)

theorem step27513 (p10 p121 p185 p194 p206 p237 p351 p836 p840 p961 : Prop)
    (h26895 : p840 ∨ p836)
    (h26851 : p237 ∨ p185)
    (h19735 : (¬ p10) ∨ (¬ p121) ∨ (¬ p194) ∨ (¬ p206) ∨ (¬ p237) ∨ (¬ p351) ∨ (¬ p840) ∨ (¬ p961)) : (¬ p961) ∨ (¬ p10) ∨ p836 ∨ (¬ p206) ∨ (¬ p194) ∨ (¬ p121) ∨ p185 ∨ (¬ p351) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19735 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u0)

theorem step27514 (p8 p290 p710 p836 p840 p1055 p1061 p1076 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26889 : p710 ∨ p8)
    (h26895 : p840 ∨ p836)
    (h17617 : (¬ p290) ∨ (¬ p710) ∨ (¬ p840) ∨ (¬ p1061) ∨ (¬ p1076)) : p1055 ∨ p8 ∨ (¬ p290) ∨ (¬ p1076) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1055) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p8) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p290 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17617 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)

theorem step27517 (p86 p185 p237 p495 p633 p636 p664 p836 p840 p1076 : Prop)
    (h26885 : p636 ∨ p633)
    (h26895 : p840 ∨ p836)
    (h26851 : p237 ∨ p185)
    (h18732 : (¬ p86) ∨ (¬ p237) ∨ (¬ p495) ∨ (¬ p636) ∨ (¬ p664) ∨ (¬ p840) ∨ (¬ p1076)) : p633 ∨ (¬ p1076) ∨ p836 ∨ (¬ p495) ∨ (¬ p86) ∨ p185 ∨ (¬ p664) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18732 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u1)

theorem step27520 (p15 p49 p84 p185 p237 p351 p420 p495 p836 p840 : Prop)
    (h26895 : p840 ∨ p836)
    (h26851 : p237 ∨ p185)
    (h18465 : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p237) ∨ (¬ p351) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p840)) : (¬ p15) ∨ (¬ p84) ∨ p836 ∨ (¬ p49) ∨ (¬ p351) ∨ (¬ p420) ∨ p185 ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18465 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u8)

theorem step27521 (p41 p45 p101 p189 p193 p286 p918 p928 : Prop)
    (h26831 : p45 ∨ p41)
    (h26901 : p928 ∨ p918)
    (h26845 : p193 ∨ p189)
    (h18669 : (¬ p45) ∨ (¬ p101) ∨ (¬ p193) ∨ (¬ p286) ∨ (¬ p928)) : (¬ p101) ∨ (¬ p286) ∨ p41 ∨ p918 ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18669 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)

theorem step27522 (p286 p1076 p1077 p1115 p1116 : Prop)
    (h26914 : (¬ p1115) ∨ (¬ p1116))
    (h26911 : p1077 ∨ p1076)
    (h13257 : (¬ p286) ∨ (¬ p1077) ∨ p1116) : (¬ p1115) ∨ p1076 ∨ (¬ p286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1116) := by
    rcases h26914 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u4 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h13257 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (u3 q2)

theorem step27523 (p286 p344 p836 p840 : Prop)
    (h26894 : (¬ p836) ∨ (¬ p840))
    (h13505 : (¬ p286) ∨ (¬ p344) ∨ p840) : (¬ p836) ∨ (¬ p344) ∨ (¬ p286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p840) := by
    rcases h26894 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h13505 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (u3 q2)

theorem step27528 (p17 p256 p519 p790 : Prop)
    (h26853 : p256 ∨ p17)
    (h10565 : (¬ p256) ∨ (¬ p519) ∨ p790) : p790 ∨ p17 ∨ (¬ p519) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p519 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h10565 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (u0 q2)

theorem step27530 (p790 p814 p819 : Prop)
    (h26892 : (¬ p790) ∨ (¬ p814))
    (h20985 : p819 ∨ p814) : p819 ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p819) := fun hu => hn (Or.inl hu)
  have u1 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p814) := by
    rcases h26892 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h20985 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step27531 (p17 p126 p224 p301 p303 p657 : Prop)
    (h26857 : p301 ∨ p126)
    (h26887 : p657 ∨ p224)
    (h19087 : (¬ p17) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p657)) : p126 ∨ p224 ∨ (¬ p17) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19087 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)

theorem step27532 (p17 p126 p189 p193 p301 p303 : Prop)
    (h26857 : p301 ∨ p126)
    (h26845 : p193 ∨ p189)
    (h21009 : (¬ p17) ∨ (¬ p193) ∨ (¬ p301) ∨ (¬ p303)) : (¬ p17) ∨ p126 ∨ p189 ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h21009 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)

theorem step27534 (p17 p126 p190 p301 p351 p662 p980 p1035 p1140 : Prop)
    (h26857 : p301 ∨ p126)
    (h17742 : (¬ p17) ∨ (¬ p190) ∨ (¬ p301) ∨ (¬ p351) ∨ (¬ p662) ∨ (¬ p980) ∨ (¬ p1035) ∨ (¬ p1140)) : (¬ p1035) ∨ p126 ∨ (¬ p662) ∨ (¬ p190) ∨ (¬ p1140) ∨ (¬ p351) ∨ (¬ p980) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p662 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17742 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u4)

theorem step27535 (p17 p126 p225 p239 p301 p351 p536 p544 p940 : Prop)
    (h26857 : p301 ∨ p126)
    (h26877 : p544 ∨ p225)
    (h17744 : (¬ p17) ∨ (¬ p239) ∨ (¬ p301) ∨ (¬ p351) ∨ (¬ p536) ∨ (¬ p544) ∨ (¬ p940)) : (¬ p940) ∨ (¬ p536) ∨ (¬ p17) ∨ (¬ p239) ∨ (¬ p351) ∨ p126 ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p239 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p126) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u8 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17744 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u0)

theorem step27536 (p17 p126 p185 p237 p286 p301 : Prop)
    (h26857 : p301 ∨ p126)
    (h26851 : p237 ∨ p185)
    (h24165 : (¬ p17) ∨ (¬ p237) ∨ (¬ p301) ∨ (¬ p286)) : p126 ∨ (¬ p17) ∨ (¬ p286) ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h24165 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step27537 (p17 p87 p126 p301 p420 p580 p601 : Prop)
    (h26857 : p301 ∨ p126)
    (h26881 : p601 ∨ p420)
    (h18781 : (¬ p17) ∨ (¬ p87) ∨ (¬ p301) ∨ (¬ p580) ∨ (¬ p601)) : p126 ∨ (¬ p580) ∨ (¬ p87) ∨ p420 ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18781 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)

theorem step27538 (p16 p17 p126 p301 p303 p665 p1095 p1096 : Prop)
    (h26857 : p301 ∨ p126)
    (h19134 : (¬ p16) ∨ (¬ p17) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p665) ∨ (¬ p1095) ∨ (¬ p1096)) : (¬ p303) ∨ p126 ∨ (¬ p17) ∨ (¬ p16) ∨ (¬ p1096) ∨ (¬ p665) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19134 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u4)

theorem step27539 (p16 p17 p126 p161 p301 p438 p1225 p1229 p1335 : Prop)
    (h26857 : p301 ∨ p126)
    (h26925 : p1225 ∨ p161)
    (h19345 : (¬ p16) ∨ (¬ p17) ∨ (¬ p301) ∨ (¬ p438) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1335)) : (¬ p438) ∨ p126 ∨ p161 ∨ (¬ p1229) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p1335) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p161) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19345 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step27541 (p17 p87 p126 p301 p382 p406 p431 p438 p816 p1385 p1393 : Prop)
    (h26857 : p301 ∨ p126)
    (h26933 : p1393 ∨ p1385)
    (h26869 : p406 ∨ p382)
    (h19643 : (¬ p17) ∨ (¬ p87) ∨ (¬ p301) ∨ (¬ p406) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p816) ∨ (¬ p1393)) : p126 ∨ (¬ p438) ∨ (¬ p87) ∨ p1385 ∨ (¬ p431) ∨ p382 ∨ (¬ p17) ∨ (¬ p816) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19643 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u9)

theorem step27542 (p10 p17 p126 p189 p193 p301 p323 : Prop)
    (h26857 : p301 ∨ p126)
    (h26845 : p193 ∨ p189)
    (h26861 : p323 ∨ p10)
    (h19967 : (¬ p17) ∨ (¬ p193) ∨ (¬ p301) ∨ (¬ p323)) : (¬ p17) ∨ p126 ∨ p189 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19967 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)

theorem step27543 (p16 p17 p126 p224 p301 p351 p595 p1286 : Prop)
    (h26857 : p301 ∨ p126)
    (h20496 : (¬ p16) ∨ (¬ p17) ∨ (¬ p224) ∨ (¬ p301) ∨ (¬ p351) ∨ (¬ p595) ∨ (¬ p1286)) : (¬ p595) ∨ p126 ∨ (¬ p17) ∨ (¬ p351) ∨ (¬ p224) ∨ (¬ p1286) ∨ (¬ p16) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20496 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u5)

theorem step27544 (p9 p16 p17 p126 p301 p303 p897 p904 p1055 p1061 p1074 : Prop)
    (h26857 : p301 ∨ p126)
    (h26909 : p1061 ∨ p1055)
    (h26899 : p904 ∨ p897)
    (h19598 : (¬ p9) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p904) ∨ (¬ p1061) ∨ (¬ p1074)) : p126 ∨ (¬ p303) ∨ (¬ p1074) ∨ (¬ p9) ∨ p1055 ∨ (¬ p17) ∨ p897 ∨ (¬ p16) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19598 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u2)

theorem step27545 (p14 p15 p16 p17 p126 p225 p301 p351 p544 : Prop)
    (h26857 : p301 ∨ p126)
    (h26877 : p544 ∨ p225)
    (h17712 : (¬ p14) ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p301) ∨ (¬ p351) ∨ (¬ p544)) : p126 ∨ p225 ∨ (¬ p14) ∨ (¬ p17) ∨ (¬ p15) ∨ (¬ p351) ∨ (¬ p16) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17712 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u8)

theorem step27546 (p15 p16 p17 p126 p301 p303 p423 p1000 : Prop)
    (h26857 : p301 ∨ p126)
    (h19226 : (¬ p15) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p423) ∨ (¬ p1000)) : p126 ∨ (¬ p15) ∨ (¬ p303) ∨ (¬ p423) ∨ (¬ p1000) ∨ (¬ p17) ∨ (¬ p16) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19226 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)

theorem step27547 (p18 p126 p210 p265 p301 p303 p1325 : Prop)
    (h26857 : p301 ∨ p126)
    (h19338 : (¬ p18) ∨ (¬ p210) ∨ p265 ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p1325)) : p265 ∨ p126 ∨ (¬ p18) ∨ (¬ p303) ∨ (¬ p210) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p265) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19338 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)

theorem step27548 (p15 p17 p39 p69 p88 p126 p225 p301 p303 p544 p883 p1096 : Prop)
    (h26877 : p544 ∨ p225)
    (h26857 : p301 ∨ p126)
    (h26833 : p69 ∨ p15)
    (h19343 : (¬ p17) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p544) ∨ (¬ p883) ∨ (¬ p1096)) : p225 ∨ (¬ p883) ∨ (¬ p88) ∨ (¬ p39) ∨ p126 ∨ p15 ∨ (¬ p303) ∨ (¬ p17) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p126) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19343 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u8)

theorem step27549 (p15 p17 p39 p69 p88 p126 p301 p303 p1000 p1145 p1229 : Prop)
    (h26857 : p301 ∨ p126)
    (h26833 : p69 ∨ p15)
    (h20067 : (¬ p17) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p1000) ∨ (¬ p1145) ∨ (¬ p1229)) : p126 ∨ (¬ p88) ∨ (¬ p1145) ∨ (¬ p303) ∨ p15 ∨ (¬ p39) ∨ (¬ p1000) ∨ (¬ p17) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1145 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20067 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u8)

theorem step27550 (p3 p163 p167 p187 : Prop)
    (h26843 : p167 ∨ p163)
    (h5458 : (¬ p3) ∨ (¬ p167) ∨ (¬ p187)) : (¬ p3) ∨ p163 ∨ (¬ p187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h5458 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)

theorem step27553 (p1325 p1328 p1333 : Prop)
    (h26930 : (¬ p1325) ∨ (¬ p1333))
    (h21460 : p1328 ∨ p1333) : p1328 ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1328) := fun hu => hn (Or.inl hu)
  have u1 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1333) := by
    rcases h26930 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h21460 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step27554 (p1325 p1330 p1333 : Prop)
    (h26930 : (¬ p1325) ∨ (¬ p1333))
    (h21644 : p1330 ∨ p1333) : p1330 ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1330) := fun hu => hn (Or.inl hu)
  have u1 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1333) := by
    rcases h26930 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h21644 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step27556 (p17 p303 p387 p518 p576 p581 p790 : Prop)
    (h26867 : p387 ∨ p303)
    (h26879 : p581 ∨ p576)
    (h19496 : (¬ p17) ∨ (¬ p387) ∨ (¬ p518) ∨ (¬ p581) ∨ (¬ p790)) : p303 ∨ (¬ p790) ∨ (¬ p518) ∨ p576 ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p518 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19496 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)

theorem step27557 (p17 p303 p387 p518 p790 p1325 p1333 : Prop)
    (h26867 : p387 ∨ p303)
    (h26931 : p1333 ∨ p1325)
    (h19497 : (¬ p17) ∨ (¬ p387) ∨ (¬ p518) ∨ (¬ p790) ∨ (¬ p1333)) : p303 ∨ p1325 ∨ (¬ p518) ∨ (¬ p790) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p518 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19497 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)

theorem step27558 (p17 p126 p256 p303 p387 p1325 p1333 : Prop)
    (h26867 : p387 ∨ p303)
    (h26931 : p1333 ∨ p1325)
    (h26853 : p256 ∨ p17)
    (h16678 : (¬ p126) ∨ (¬ p256) ∨ (¬ p387) ∨ (¬ p1333)) : p303 ∨ p1325 ∨ p17 ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16678 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step27559 (p17 p126 p224 p256 p303 p387 : Prop)
    (h26867 : p387 ∨ p303)
    (h26853 : p256 ∨ p17)
    (h18102 : (¬ p126) ∨ (¬ p224) ∨ (¬ p256) ∨ (¬ p387)) : p303 ∨ (¬ p224) ∨ p17 ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18102 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step27560 (p8 p224 p303 p308 p349 p387 p710 : Prop)
    (h26867 : p387 ∨ p303)
    (h26889 : p710 ∨ p8)
    (h16785 : (¬ p224) ∨ (¬ p308) ∨ (¬ p349) ∨ (¬ p387) ∨ (¬ p710)) : p303 ∨ p8 ∨ (¬ p224) ∨ (¬ p349) ∨ (¬ p308) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p8) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p308 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16785 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step27561 (p224 p303 p387 p420 p601 p633 p636 : Prop)
    (h26867 : p387 ∨ p303)
    (h26885 : p636 ∨ p633)
    (h26881 : p601 ∨ p420)
    (h17279 : (¬ p224) ∨ (¬ p387) ∨ (¬ p601) ∨ (¬ p636)) : p303 ∨ p633 ∨ (¬ p224) ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p633) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17279 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)

theorem step27562 (p124 p125 p224 p303 p304 p362 p387 : Prop)
    (h26867 : p387 ∨ p303)
    (h26859 : p304 ∨ p124)
    (h26865 : p362 ∨ p125)
    (h19172 : (¬ p224) ∨ (¬ p304) ∨ (¬ p362) ∨ (¬ p387)) : p303 ∨ p124 ∨ (¬ p224) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19172 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)

theorem step27563 (p303 p367 p382 p387 : Prop)
    (h26867 : p387 ∨ p303)
    (h10100 : (¬ p367) ∨ (¬ p382) ∨ (¬ p387)) : p303 ∨ (¬ p382) ∨ (¬ p367) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p367 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h10100 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step27564 (p303 p367 p382 p387 p406 : Prop)
    (h26867 : p387 ∨ p303)
    (h26868 : (¬ p382) ∨ (¬ p406))
    (h14426 : (¬ p367) ∨ (¬ p387) ∨ p406) : p303 ∨ (¬ p367) ∨ (¬ p382) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p367 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : (¬ p406) := by
    rcases h26868 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h14426 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (u4 q2)

theorem step27566 (p124 p125 p303 p304 p362 p387 p419 : Prop)
    (h26867 : p387 ∨ p303)
    (h26859 : p304 ∨ p124)
    (h26865 : p362 ∨ p125)
    (h17692 : (¬ p304) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p419)) : p303 ∨ p124 ∨ (¬ p419) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17692 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step27567 (p101 p102 p126 p258 p303 p387 : Prop)
    (h26867 : p387 ∨ p303)
    (h26837 : p102 ∨ p101)
    (h19459 : (¬ p102) ∨ (¬ p126) ∨ (¬ p258) ∨ (¬ p387)) : p303 ∨ (¬ p258) ∨ (¬ p126) ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19459 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step27568 (p101 p102 p124 p125 p303 p304 p362 p387 : Prop)
    (h26867 : p387 ∨ p303)
    (h26859 : p304 ∨ p124)
    (h26837 : p102 ∨ p101)
    (h26865 : p362 ∨ p125)
    (h18507 : (¬ p102) ∨ (¬ p304) ∨ (¬ p362) ∨ (¬ p387)) : p303 ∨ p124 ∨ p101 ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18507 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)

theorem step27569 (p124 p224 p261 p304 p344 p346 p1325 : Prop)
    (h26859 : p304 ∨ p124)
    (h26863 : p346 ∨ p344)
    (h20101 : (¬ p224) ∨ (¬ p261) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p1325)) : p124 ∨ p344 ∨ (¬ p224) ∨ (¬ p261) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20101 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)

theorem step27570 (p3 p224 p225 p226 p1325 : Prop)
    (h26847 : p226 ∨ p3)
    (h19749 : (¬ p224) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p1325)) : p3 ∨ (¬ p225) ∨ (¬ p224) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19749 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)

theorem step27571 (p185 p237 p980 p983 p1115 p1116 p1325 : Prop)
    (h26903 : p983 ∨ p980)
    (h26851 : p237 ∨ p185)
    (h26915 : p1116 ∨ p1115)
    (h20157 : (¬ p237) ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1325)) : p980 ∨ p185 ∨ p1115 ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20157 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)

theorem step27573 (p10 p121 p125 p211 p362 p1452 : Prop)
    (h26865 : p362 ∨ p125)
    (h19665 : (¬ p10) ∨ (¬ p121) ∨ (¬ p211) ∨ (¬ p362) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p10) ∨ (¬ p121) ∨ p125 ∨ (¬ p211) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19665 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step27574 (p64 p185 p918 p928 p1140 p1159 p1346 p1452 p1465 p1490 : Prop)
    (h26901 : p928 ∨ p918)
    (h26919 : p1159 ∨ p1140)
    (h19708 : (¬ p64) ∨ (¬ p185) ∨ (¬ p928) ∨ (¬ p1159) ∨ (¬ p1346) ∨ (¬ p1452) ∨ (¬ p1465) ∨ (¬ p1490)) : (¬ p1346) ∨ p918 ∨ (¬ p1452) ∨ (¬ p64) ∨ (¬ p1490) ∨ (¬ p185) ∨ (¬ p1465) ∨ p1140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1490 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19708 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u4)

theorem step27576 (p124 p227 p304 p980 p1452 : Prop)
    (h26859 : p304 ∨ p124)
    (h18922 : (¬ p227) ∨ (¬ p304) ∨ (¬ p980) ∨ (¬ p1452)) : (¬ p227) ∨ (¬ p1452) ∨ (¬ p980) ∨ p124 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18922 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)

theorem step27577 (p121 p134 p142 p189 p193 p1452 : Prop)
    (h26845 : p193 ∨ p189)
    (h26841 : p142 ∨ p134)
    (h16723 : (¬ p121) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p121) ∨ p189 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16723 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step27578 (p11 p258 p980 p1443 p1452 : Prop)
    (h26935 : p1443 ∨ p11)
    (h19993 : (¬ p258) ∨ (¬ p980) ∨ (¬ p1443) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p258) ∨ p11 ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19993 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step27581 (p11 p258 p1325 p1443 p1452 : Prop)
    (h26935 : p1443 ∨ p11)
    (h19992 : (¬ p258) ∨ (¬ p1325) ∨ (¬ p1443) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p258) ∨ (¬ p1325) ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19992 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step27582 (p13 p769 p979 p1055 p1061 p1452 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h17263 : (¬ p13) ∨ (¬ p769) ∨ (¬ p979) ∨ (¬ p1061) ∨ (¬ p1452)) : (¬ p769) ∨ (¬ p979) ∨ (¬ p1452) ∨ (¬ p13) ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p979 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17263 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)

theorem step27584 (p386 p517 p789 p858 p1325 p1452 : Prop)
    (h26897 : p858 ∨ p789)
    (h16507 : (¬ p386) ∨ (¬ p517) ∨ (¬ p858) ∨ (¬ p1325) ∨ (¬ p1452)) : (¬ p517) ∨ (¬ p1452) ∨ (¬ p386) ∨ (¬ p1325) ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p517 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p386 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16507 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)

theorem step27587 (p455 p633 p636 p980 p1452 : Prop)
    (h26885 : p636 ∨ p633)
    (h19248 : (¬ p455) ∨ (¬ p636) ∨ (¬ p980) ∨ (¬ p1452)) : (¬ p1452) ∨ p633 ∨ (¬ p455) ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p633) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19248 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)

theorem step27590 (p227 p496 p1074 p1096 p1099 p1325 p1452 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h25792 : (¬ p1099) ∨ (¬ p496) ∨ (¬ p227) ∨ (¬ p1074) ∨ (¬ p1452) ∨ (¬ p1325)) : (¬ p1452) ∨ (¬ p496) ∨ (¬ p1074) ∨ (¬ p227) ∨ p1096 ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25792 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u5)

theorem step27591 (p6 p10 p127 p323 p386 p1325 p1452 : Prop)
    (h26861 : p323 ∨ p10)
    (h26839 : p127 ∨ p6)
    (h19078 : (¬ p127) ∨ (¬ p323) ∨ (¬ p386) ∨ (¬ p1325) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p386) ∨ p10 ∨ p6 ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p386 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19078 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)

theorem step27592 (p1001 p1325 p1333 p1465 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h10606 : (¬ p1001) ∨ (¬ p1333) ∨ (¬ p1465)) : (¬ p1001) ∨ p1325 ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1001 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h10606 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)

theorem step27593 (p189 p424 p796 p997 p1325 p1333 p1465 : Prop)
    (h26891 : p796 ∨ p424)
    (h26931 : p1333 ∨ p1325)
    (h19788 : (¬ p189) ∨ (¬ p796) ∨ (¬ p997) ∨ (¬ p1333) ∨ (¬ p1465)) : p424 ∨ p1325 ∨ (¬ p997) ∨ (¬ p1465) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p997 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19788 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)

theorem step27594 (p6 p127 p1140 p1159 p1465 p1508 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26839 : p127 ∨ p6)
    (h19271 : (¬ p127) ∨ (¬ p1159) ∨ (¬ p1465) ∨ (¬ p1508)) : p1140 ∨ (¬ p1465) ∨ (¬ p1508) ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19271 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)

theorem step27595 (p3 p980 p983 p1140 p1159 p1465 : Prop)
    (h26903 : p983 ∨ p980)
    (h26919 : p1159 ∨ p1140)
    (h19899 : (¬ p3) ∨ (¬ p983) ∨ (¬ p1159) ∨ (¬ p1465)) : p980 ∨ p1140 ∨ (¬ p1465) ∨ (¬ p3) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1140) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19899 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)

theorem step27596 (p11 p126 p301 p1443 p1452 p1465 : Prop)
    (h26857 : p301 ∨ p126)
    (h26935 : p1443 ∨ p11)
    (h20513 : (¬ p301) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p1465)) : p126 ∨ (¬ p1452) ∨ (¬ p1465) ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20513 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)

theorem step27598 (p17 p126 p194 p256 p434 p1140 p1159 p1330 p1465 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26853 : p256 ∨ p17)
    (h18213 : (¬ p126) ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p434) ∨ (¬ p1159) ∨ (¬ p1330) ∨ (¬ p1465)) : p1140 ∨ (¬ p434) ∨ (¬ p126) ∨ (¬ p1465) ∨ (¬ p194) ∨ p17 ∨ (¬ p1330) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18213 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step27599 (p124 p194 p266 p344 p728 p1140 p1159 p1330 p1465 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h19509 : (¬ p124) ∨ (¬ p194) ∨ (¬ p266) ∨ (¬ p344) ∨ (¬ p728) ∨ (¬ p1159) ∨ (¬ p1330) ∨ (¬ p1465)) : (¬ p728) ∨ p1140 ∨ (¬ p1465) ∨ (¬ p124) ∨ (¬ p194) ∨ (¬ p266) ∨ (¬ p344) ∨ (¬ p1330) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1140) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19509 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u2)

theorem step27600 (p15 p69 p423 p1141 p1325 p1333 p1465 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26931 : p1333 ∨ p1325)
    (h26833 : p69 ∨ p15)
    (h17193 : (¬ p69) ∨ (¬ p1141) ∨ (¬ p1333) ∨ (¬ p1465)) : p423 ∨ p1325 ∨ (¬ p1465) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17193 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)

theorem step27601 (p189 p422 p1325 p1333 p1465 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h19811 : (¬ p189) ∨ (¬ p422) ∨ (¬ p1333) ∨ (¬ p1465)) : p1325 ∨ (¬ p422) ∨ (¬ p189) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19811 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)

theorem step27602 (p125 p189 p263 p362 p422 p434 p1330 p1465 : Prop)
    (h26865 : p362 ∨ p125)
    (h19475 : (¬ p189) ∨ (¬ p263) ∨ (¬ p362) ∨ (¬ p422) ∨ (¬ p434) ∨ (¬ p1330) ∨ (¬ p1465)) : (¬ p422) ∨ (¬ p434) ∨ (¬ p189) ∨ (¬ p1330) ∨ (¬ p263) ∨ p125 ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p263 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19475 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step27603 (p17 p189 p256 p422 p1465 : Prop)
    (h26853 : p256 ∨ p17)
    (h17949 : (¬ p189) ∨ (¬ p256) ∨ (¬ p422) ∨ (¬ p1465)) : (¬ p422) ∨ (¬ p1465) ∨ p17 ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17949 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)

theorem step27604 (p980 p983 p1041 p1465 : Prop)
    (h26903 : p983 ∨ p980)
    (h14499 : (¬ p983) ∨ (¬ p1041) ∨ (¬ p1465)) : (¬ p1041) ∨ p980 ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1041 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h14499 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)

theorem step27608 (p17 p121 p143 p1206 p1346 p1495 : Prop)
    (h26923 : p1206 ∨ p121)
    (h19187 : (¬ p17) ∨ (¬ p143) ∨ (¬ p1206) ∨ (¬ p1346) ∨ (¬ p1495)) : p121 ∨ (¬ p1346) ∨ (¬ p1495) ∨ (¬ p143) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19187 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)

theorem step27609 (p11 p17 p101 p102 p121 p256 p1206 p1443 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26935 : p1443 ∨ p11)
    (h26837 : p102 ∨ p101)
    (h26853 : p256 ∨ p17)
    (h16496 : (¬ p102) ∨ (¬ p256) ∨ (¬ p1206) ∨ (¬ p1443)) : p121 ∨ p11 ∨ p101 ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p11) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16496 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step27610 (p101 p102 p121 p344 p664 p1079 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26837 : p102 ∨ p101)
    (h16333 : (¬ p102) ∨ (¬ p344) ∨ (¬ p664) ∨ (¬ p1079) ∨ (¬ p1206)) : p121 ∨ (¬ p1079) ∨ (¬ p664) ∨ p101 ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p1079 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16333 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)

theorem step27611 (p101 p102 p121 p211 p227 p344 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26837 : p102 ∨ p101)
    (h17611 : (¬ p102) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p344) ∨ (¬ p1206)) : p121 ∨ (¬ p227) ∨ p101 ∨ (¬ p211) ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17611 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step27613 (p6 p11 p121 p141 p191 p1206 p1443 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26935 : p1443 ∨ p11)
    (h19572 : (¬ p6) ∨ (¬ p141) ∨ (¬ p191) ∨ (¬ p1206) ∨ (¬ p1443)) : p121 ∨ p11 ∨ (¬ p6) ∨ (¬ p141) ∨ (¬ p191) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p11) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19572 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step27614 (p11 p17 p121 p170 p185 p256 p1206 p1443 : Prop)
    (h26935 : p1443 ∨ p11)
    (h26923 : p1206 ∨ p121)
    (h26853 : p256 ∨ p17)
    (h20160 : (¬ p170) ∨ (¬ p185) ∨ (¬ p256) ∨ (¬ p1206) ∨ (¬ p1443)) : (¬ p185) ∨ p11 ∨ p121 ∨ (¬ p170) ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p11) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20160 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step27615 (p2 p3 p226 p539 : Prop)
    (h26847 : p226 ∨ p3)
    (h15487 : p2 ∨ (¬ p226) ∨ (¬ p539)) : p3 ∨ (¬ p539) ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p539 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p2) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h15487 with q0 | q1 | q2
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)

theorem step27616 (p125 p209 p303 p329 p419 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h18935 : (¬ p125) ∨ (¬ p209) ∨ (¬ p303) ∨ (¬ p329) ∨ (¬ p996)) : p419 ∨ (¬ p125) ∨ (¬ p329) ∨ (¬ p303) ∨ (¬ p209) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p329 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18935 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step27617 (p134 p329 p424 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h14275 : p134 ∨ (¬ p329) ∨ (¬ p796)) : p424 ∨ p134 ∨ (¬ p329) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p134) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p329 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h14275 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step27618 (p3 p10 p125 p163 p211 p226 p362 : Prop)
    (h26865 : p362 ∨ p125)
    (h26847 : p226 ∨ p3)
    (h19601 : (¬ p10) ∨ (¬ p163) ∨ (¬ p211) ∨ (¬ p226) ∨ (¬ p362)) : p125 ∨ (¬ p10) ∨ (¬ p163) ∨ p3 ∨ (¬ p211) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p125) := fun hu => hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19601 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step27633 (p423 p1141 p1145 : Prop)
    (h26916 : (¬ p423) ∨ (¬ p1141))
    (h21560 : p1145 ∨ p1141) : p1145 ∨ (¬ p423) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1145) := fun hu => hn (Or.inl hu)
  have u1 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1141) := by
    rcases h26916 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h21560 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step27634 (p38 p423 p1140 p1141 p1159 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26916 : (¬ p423) ∨ (¬ p1141))
    (h14347 : (¬ p38) ∨ p1141 ∨ (¬ p1159)) : p1140 ∨ (¬ p423) ∨ (¬ p38) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : (¬ p1141) := by
    rcases h26916 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h14347 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u3)

theorem step27648 (p192 p422 p1140 p1159 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h13779 : (¬ p192) ∨ p422 ∨ (¬ p1159)) : p1140 ∨ p422 ∨ (¬ p192) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h13779 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)

theorem step27649 (p163 p167 p422 p1037 : Prop)
    (h26843 : p167 ∨ p163)
    (h13305 : (¬ p167) ∨ p422 ∨ (¬ p1037)) : (¬ p1037) ∨ p163 ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1037 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h13305 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u0)

theorem step27650 (p17 p137 p189 p193 p422 p1213 p1256 : Prop)
    (h26845 : p193 ∨ p189)
    (h26929 : p1256 ∨ p422)
    (h16822 : (¬ p17) ∨ (¬ p137) ∨ (¬ p193) ∨ (¬ p1213) ∨ (¬ p1256)) : p189 ∨ p422 ∨ (¬ p17) ∨ (¬ p1213) ∨ (¬ p137) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p189) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p137 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16822 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)

theorem step27654 (p5 p134 p303 p387 p420 p422 p495 p499 p601 p1140 p1159 p1256 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26881 : p601 ∨ p420)
    (h26867 : p387 ∨ p303)
    (h26929 : p1256 ∨ p422)
    (h26875 : p499 ∨ p495)
    (h18169 : (¬ p5) ∨ (¬ p134) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1159) ∨ (¬ p1256)) : p1140 ∨ (¬ p5) ∨ p420 ∨ p303 ∨ (¬ p134) ∨ p422 ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18169 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u10)

theorem step27656 (p134 p422 p1207 p1256 : Prop)
    (h26929 : p1256 ∨ p422)
    (h11576 : (¬ p134) ∨ (¬ p1207) ∨ (¬ p1256)) : (¬ p1207) ∨ p422 ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h11576 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)

theorem step27657 (p6 p192 p422 p1207 p1256 : Prop)
    (h26929 : p1256 ∨ p422)
    (h11960 : (¬ p6) ∨ (¬ p192) ∨ (¬ p1207) ∨ (¬ p1256)) : (¬ p1207) ∨ p422 ∨ (¬ p6) ∨ (¬ p192) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h11960 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step27658 (p134 p142 p234 p326 p422 p423 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26841 : p142 ∨ p134)
    (h18680 : (¬ p142) ∨ (¬ p326) ∨ (¬ p422) ∨ (¬ p423) ∨ (¬ p1187)) : p234 ∨ (¬ p423) ∨ p134 ∨ (¬ p326) ∨ (¬ p422) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18680 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)

theorem step27659 (p18 p19 p423 p1207 : Prop)
    (h26828 : (¬ p18) ∨ (¬ p19))
    (h14536 : p19 ∨ (¬ p423) ∨ (¬ p1207)) : (¬ p1207) ∨ (¬ p423) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p19) := by
    rcases h26828 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h14536 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)

theorem step27660 (p83 p423 p790 p814 p980 p1035 p1124 p1249 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h26893 : p814 ∨ p790)
    (h19272 : (¬ p83) ∨ (¬ p423) ∨ (¬ p814) ∨ (¬ p980) ∨ (¬ p1035) ∨ (¬ p1124) ∨ (¬ p1249) ∨ (¬ p1393)) : p1385 ∨ (¬ p423) ∨ (¬ p1035) ∨ p790 ∨ (¬ p83) ∨ (¬ p1249) ∨ (¬ p980) ∨ (¬ p1124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1385) := fun hu => hn (Or.inl hu)
  have u1 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19272 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u8)

theorem step27661 (p14 p225 p229 p423 p1140 p1159 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26849 : p229 ∨ p14)
    (h17175 : (¬ p225) ∨ (¬ p229) ∨ (¬ p423) ∨ (¬ p1159)) : (¬ p423) ∨ p1140 ∨ (¬ p225) ∨ p14 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1140) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17175 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step27662 (p6 p14 p127 p229 p423 p1140 p1159 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26849 : p229 ∨ p14)
    (h26839 : p127 ∨ p6)
    (h18919 : (¬ p127) ∨ (¬ p229) ∨ (¬ p423) ∨ (¬ p1159)) : (¬ p423) ∨ p1140 ∨ p14 ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1140) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18919 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step27663 (p234 p303 p331 p423 p1001 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h18857 : (¬ p303) ∨ (¬ p331) ∨ (¬ p423) ∨ (¬ p1001) ∨ (¬ p1187)) : p234 ∨ (¬ p423) ∨ (¬ p303) ∨ (¬ p331) ∨ (¬ p1001) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1001 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18857 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step27665 (p234 p423 p1035 p1187 p1325 : Prop)
    (h26921 : p1187 ∨ p234)
    (h17163 : (¬ p423) ∨ (¬ p1035) ∨ (¬ p1187) ∨ (¬ p1325)) : p234 ∨ (¬ p423) ∨ (¬ p1325) ∨ (¬ p1035) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17163 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step27666 (p20 p126 p188 p420 p423 p1140 p1159 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h19773 : (¬ p20) ∨ (¬ p126) ∨ (¬ p188) ∨ (¬ p420) ∨ (¬ p423) ∨ (¬ p1159)) : p1140 ∨ (¬ p420) ∨ (¬ p126) ∨ (¬ p20) ∨ (¬ p423) ∨ (¬ p188) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p20 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19773 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)

theorem step27668 (p18 p19 p330 : Prop)
    (h26829 : p19 ∨ p18)
    (h17321 : (¬ p19) ∨ p330) : p18 ∨ p330 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p18) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p330) := fun hu => hn (Or.inr hu)
  have u2 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17321 with q0 | q1
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)

theorem step27669 (p18 p19 p423 p1141 p1325 p1333 p1465 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26931 : p1333 ∨ p1325)
    (h26829 : p19 ∨ p18)
    (h19125 : (¬ p19) ∨ (¬ p1141) ∨ (¬ p1333) ∨ (¬ p1465)) : p423 ∨ p1325 ∨ p18 ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19125 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)

theorem step27670 (p18 p19 p423 p1141 p1212 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26829 : p19 ∨ p18)
    (h11355 : (¬ p19) ∨ (¬ p1141) ∨ (¬ p1212)) : p423 ∨ (¬ p1212) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p1212 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h11355 with q0 | q1 | q2
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)

theorem step27672 (p18 p19 p234 p329 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26829 : p19 ∨ p18)
    (h12233 : (¬ p19) ∨ (¬ p329) ∨ (¬ p1187)) : p234 ∨ p18 ∨ (¬ p329) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p329 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h12233 with q0 | q1 | q2
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step27676 (p18 p19 p134 p303 p328 p387 p424 : Prop)
    (h26867 : p387 ∨ p303)
    (h26829 : p19 ∨ p18)
    (h16941 : (¬ p19) ∨ (¬ p134) ∨ (¬ p328) ∨ (¬ p387) ∨ (¬ p424)) : (¬ p424) ∨ p303 ∨ (¬ p134) ∨ (¬ p328) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p328 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16941 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step27677 (p18 p19 p121 p124 p961 : Prop)
    (h26829 : p19 ∨ p18)
    (h17438 : (¬ p19) ∨ (¬ p121) ∨ (¬ p124) ∨ (¬ p961)) : (¬ p121) ∨ (¬ p961) ∨ (¬ p124) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17438 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)

theorem step27678 (p17 p18 p19 p50 p137 p189 p193 : Prop)
    (h26845 : p193 ∨ p189)
    (h26829 : p19 ∨ p18)
    (h16906 : (¬ p17) ∨ (¬ p19) ∨ (¬ p50) ∨ (¬ p137) ∨ (¬ p193)) : (¬ p17) ∨ p189 ∨ (¬ p50) ∨ (¬ p137) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p50 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p137 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16906 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step27679 (p16 p17 p18 p19 p258 p344 p346 p382 p406 p620 p1188 p1287 : Prop)
    (h26829 : p19 ∨ p18)
    (h26863 : p346 ∨ p344)
    (h26869 : p406 ∨ p382)
    (h20501 : (¬ p16) ∨ (¬ p17) ∨ (¬ p19) ∨ (¬ p258) ∨ (¬ p346) ∨ (¬ p406) ∨ (¬ p620) ∨ (¬ p1188) ∨ (¬ p1287)) : (¬ p1188) ∨ (¬ p620) ∨ (¬ p16) ∨ p18 ∨ (¬ p1287) ∨ (¬ p258) ∨ p344 ∨ p382 ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p620 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20501 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u4)

theorem step27680 (p9 p16 p17 p18 p19 p126 p301 p303 p879 p1055 p1061 p1074 : Prop)
    (h26857 : p301 ∨ p126)
    (h26829 : p19 ∨ p18)
    (h26909 : p1061 ∨ p1055)
    (h19599 : (¬ p9) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p19) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p879) ∨ (¬ p1061) ∨ (¬ p1074)) : p126 ∨ (¬ p1074) ∨ (¬ p303) ∨ p18 ∨ (¬ p17) ∨ (¬ p9) ∨ (¬ p16) ∨ (¬ p879) ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p879 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h19599 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u1)

theorem step27681 (p3 p14 p16 p17 p18 p19 p71 p126 p229 p301 p303 : Prop)
    (h26849 : p229 ∨ p14)
    (h26857 : p301 ∨ p126)
    (h26829 : p19 ∨ p18)
    (h19113 : (¬ p3) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p19) ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p301) ∨ (¬ p303)) : p14 ∨ (¬ p3) ∨ (¬ p16) ∨ p126 ∨ (¬ p71) ∨ (¬ p17) ∨ (¬ p303) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p126) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19113 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u6)

theorem step27682 (p18 p19 p50 p125 p126 p136 p207 p301 p362 : Prop)
    (h26857 : p301 ∨ p126)
    (h26829 : p19 ∨ p18)
    (h26865 : p362 ∨ p125)
    (h17172 : (¬ p19) ∨ (¬ p50) ∨ (¬ p136) ∨ (¬ p207) ∨ (¬ p301) ∨ (¬ p362)) : p126 ∨ p18 ∨ (¬ p207) ∨ (¬ p50) ∨ p125 ∨ (¬ p136) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p50 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p136 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17172 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u8)

theorem step27683 (p16 p18 p19 p71 p125 p126 p143 p261 p423 p1140 p1141 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26829 : p19 ∨ p18)
    (h19119 : (¬ p16) ∨ (¬ p19) ∨ (¬ p71) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p143) ∨ (¬ p261) ∨ (¬ p1140) ∨ (¬ p1141)) : p423 ∨ (¬ p125) ∨ p18 ∨ (¬ p1140) ∨ (¬ p143) ∨ (¬ p126) ∨ (¬ p261) ∨ (¬ p16) ∨ (¬ p71) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19119 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u3)
  · exact False.elim (q8 u9)

theorem step27684 (p16 p18 p19 p71 p185 p224 p423 p836 p1140 p1141 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26829 : p19 ∨ p18)
    (h20092 : (¬ p16) ∨ (¬ p19) ∨ (¬ p71) ∨ (¬ p185) ∨ (¬ p224) ∨ (¬ p836) ∨ (¬ p1140) ∨ (¬ p1141)) : (¬ p836) ∨ p423 ∨ (¬ p16) ∨ (¬ p224) ∨ p18 ∨ (¬ p71) ∨ (¬ p185) ∨ (¬ p1140) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p423) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20092 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u8)

theorem step27685 (p6 p18 p19 p64 p885 p1096 : Prop)
    (h26829 : p19 ∨ p18)
    (h16732 : (¬ p6) ∨ (¬ p19) ∨ (¬ p64) ∨ (¬ p885) ∨ (¬ p1096)) : (¬ p64) ∨ (¬ p885) ∨ p18 ∨ (¬ p6) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p885 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16732 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)

theorem step27686 (p6 p18 p19 p64 p224 p234 p382 p406 p545 p617 p1187 : Prop)
    (h26869 : p406 ∨ p382)
    (h26921 : p1187 ∨ p234)
    (h26829 : p19 ∨ p18)
    (h17992 : (¬ p6) ∨ (¬ p19) ∨ (¬ p64) ∨ (¬ p224) ∨ (¬ p406) ∨ (¬ p545) ∨ (¬ p617) ∨ (¬ p1187)) : p382 ∨ (¬ p545) ∨ (¬ p617) ∨ p234 ∨ (¬ p6) ∨ (¬ p64) ∨ (¬ p224) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h17992 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u9)

theorem step27688 (p6 p18 p19 p64 p86 p234 p789 p790 p1187 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26829 : p19 ∨ p18)
    (h26921 : p1187 ∨ p234)
    (h18006 : (¬ p6) ∨ (¬ p19) ∨ (¬ p64) ∨ (¬ p86) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1187) ∨ (¬ p1333)) : (¬ p789) ∨ p1325 ∨ p18 ∨ (¬ p790) ∨ p234 ∨ (¬ p86) ∨ (¬ p64) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18006 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u8)

theorem step27690 (p6 p18 p19 p64 p86 p185 p234 p237 p545 p836 p840 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26829 : p19 ∨ p18)
    (h26895 : p840 ∨ p836)
    (h26851 : p237 ∨ p185)
    (h18691 : (¬ p6) ∨ (¬ p19) ∨ (¬ p64) ∨ (¬ p86) ∨ (¬ p237) ∨ (¬ p545) ∨ (¬ p840) ∨ (¬ p1187)) : p234 ∨ (¬ p545) ∨ (¬ p86) ∨ p18 ∨ (¬ p64) ∨ (¬ p6) ∨ p836 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18691 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u8)

theorem step27691 (p6 p18 p19 p64 p160 p423 p980 p1044 p1141 p1273 p1348 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26829 : p19 ∨ p18)
    (h18715 : (¬ p6) ∨ (¬ p19) ∨ (¬ p64) ∨ (¬ p160) ∨ (¬ p980) ∨ (¬ p1044) ∨ (¬ p1141) ∨ (¬ p1273) ∨ (¬ p1348)) : p423 ∨ (¬ p160) ∨ (¬ p6) ∨ (¬ p1273) ∨ p18 ∨ (¬ p1348) ∨ (¬ p64) ∨ (¬ p980) ∨ (¬ p1044) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18715 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u3)
  · exact False.elim (q8 u5)

theorem step27692 (p6 p8 p18 p19 p64 p423 p710 p897 p904 p1044 p1055 p1061 p1141 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26829 : p19 ∨ p18)
    (h26909 : p1061 ∨ p1055)
    (h26899 : p904 ∨ p897)
    (h26889 : p710 ∨ p8)
    (h20319 : (¬ p6) ∨ (¬ p19) ∨ (¬ p64) ∨ (¬ p710) ∨ (¬ p904) ∨ (¬ p1044) ∨ (¬ p1061) ∨ (¬ p1141)) : p423 ∨ p18 ∨ (¬ p6) ∨ p1055 ∨ (¬ p1044) ∨ p897 ∨ (¬ p64) ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u12 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20319 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u12)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u8)

theorem step27694 (p2 p18 p19 p67 p125 p207 p362 p419 p434 : Prop)
    (h26865 : p362 ∨ p125)
    (h26829 : p19 ∨ p18)
    (h25799 : (¬ p207) ∨ (¬ p19) ∨ (¬ p434) ∨ (¬ p2) ∨ (¬ p419) ∨ (¬ p362) ∨ (¬ p67)) : (¬ p2) ∨ (¬ p434) ∨ (¬ p419) ∨ (¬ p207) ∨ p125 ∨ (¬ p67) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u8 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h25799 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u5)

theorem step27695 (p18 p19 p48 p87 p134 p189 : Prop)
    (h26829 : p19 ∨ p18)
    (h16266 : (¬ p19) ∨ (¬ p48) ∨ (¬ p87) ∨ (¬ p134) ∨ (¬ p189)) : (¬ p189) ∨ p18 ∨ (¬ p134) ∨ (¬ p87) ∨ (¬ p48) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16266 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)

theorem step27696 (p18 p19 p125 p185 p207 p303 p362 p387 p864 p918 p928 p1249 : Prop)
    (h26867 : p387 ∨ p303)
    (h26865 : p362 ∨ p125)
    (h26901 : p928 ∨ p918)
    (h26829 : p19 ∨ p18)
    (h19410 : (¬ p19) ∨ (¬ p185) ∨ (¬ p207) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p864) ∨ (¬ p928) ∨ (¬ p1249)) : (¬ p864) ∨ p303 ∨ (¬ p1249) ∨ p125 ∨ p918 ∨ (¬ p207) ∨ p18 ∨ (¬ p185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19410 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u11)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u2)

theorem step27697 (p18 p19 p234 p434 p435 p1187 : Prop)
    (h26829 : p19 ∨ p18)
    (h26921 : p1187 ∨ p234)
    (h20396 : (¬ p19) ∨ (¬ p434) ∨ (¬ p435) ∨ (¬ p1187)) : (¬ p434) ∨ (¬ p435) ∨ p18 ∨ p234 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20396 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)

theorem step27698 (p15 p18 p19 p121 p1452 : Prop)
    (h26829 : p19 ∨ p18)
    (h17778 : (¬ p15) ∨ (¬ p19) ∨ (¬ p121) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p15) ∨ p18 ∨ (¬ p121) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17778 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)

theorem step27700 (p8 p15 p18 p19 p121 p224 p228 p710 p1103 : Prop)
    (h26829 : p19 ∨ p18)
    (h26889 : p710 ∨ p8)
    (h18672 : (¬ p15) ∨ (¬ p19) ∨ (¬ p121) ∨ (¬ p224) ∨ (¬ p228) ∨ (¬ p710) ∨ (¬ p1103)) : (¬ p15) ∨ (¬ p121) ∨ (¬ p224) ∨ (¬ p228) ∨ p18 ∨ (¬ p1103) ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u8 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18672 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u5)

theorem step27701 (p15 p18 p19 p121 p228 p1226 p1237 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26829 : p19 ∨ p18)
    (h18674 : (¬ p15) ∨ (¬ p19) ∨ (¬ p121) ∨ (¬ p228) ∨ (¬ p1226) ∨ (¬ p1237) ∨ (¬ p1333)) : p1325 ∨ (¬ p1226) ∨ (¬ p1237) ∨ (¬ p228) ∨ p18 ∨ (¬ p15) ∨ (¬ p121) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18674 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u7)

theorem step27702 (p2 p18 p19 p38 p224 p419 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h26829 : p19 ∨ p18)
    (h16538 : (¬ p2) ∨ (¬ p19) ∨ (¬ p38) ∨ (¬ p419) ∨ (¬ p657)) : (¬ p2) ∨ p224 ∨ (¬ p38) ∨ (¬ p419) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16538 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step27704 (p2 p18 p19 p38 p126 p143 p325 : Prop)
    (h26829 : p19 ∨ p18)
    (h19135 : (¬ p2) ∨ (¬ p19) ∨ (¬ p38) ∨ (¬ p126) ∨ (¬ p143) ∨ (¬ p325)) : (¬ p325) ∨ (¬ p38) ∨ p18 ∨ (¬ p126) ∨ (¬ p143) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19135 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u0)

theorem step27705 (p18 p19 p101 p102 p423 p1140 p1141 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26837 : p102 ∨ p101)
    (h26829 : p19 ∨ p18)
    (h18657 : (¬ p19) ∨ (¬ p102) ∨ (¬ p1140) ∨ (¬ p1141)) : p423 ∨ (¬ p1140) ∨ p101 ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18657 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step27706 (p15 p18 p19 p101 p102 p344 : Prop)
    (h26829 : p19 ∨ p18)
    (h26837 : p102 ∨ p101)
    (h17379 : (¬ p15) ∨ (¬ p19) ∨ (¬ p102) ∨ (¬ p344)) : (¬ p15) ∨ (¬ p344) ∨ p18 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17379 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)

theorem step27707 (p15 p18 p19 p101 p102 p1076 p1077 : Prop)
    (h26837 : p102 ∨ p101)
    (h26829 : p19 ∨ p18)
    (h26911 : p1077 ∨ p1076)
    (h17440 : (¬ p15) ∨ (¬ p19) ∨ (¬ p102) ∨ (¬ p1077)) : (¬ p15) ∨ p101 ∨ p18 ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17440 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)

theorem step27708 (p15 p18 p19 p101 p102 p290 p1055 p1103 p1115 p1116 : Prop)
    (h26837 : p102 ∨ p101)
    (h26915 : p1116 ∨ p1115)
    (h26829 : p19 ∨ p18)
    (h17724 : (¬ p15) ∨ (¬ p19) ∨ (¬ p102) ∨ (¬ p290) ∨ (¬ p1055) ∨ (¬ p1103) ∨ (¬ p1116)) : (¬ p15) ∨ (¬ p290) ∨ p101 ∨ (¬ p1055) ∨ (¬ p1103) ∨ p1115 ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p290 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u9 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17724 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u8)

theorem step27709 (p15 p18 p19 p101 p102 p265 p576 p918 p928 p961 p1080 : Prop)
    (h26901 : p928 ∨ p918)
    (h26837 : p102 ∨ p101)
    (h26829 : p19 ∨ p18)
    (h18670 : (¬ p15) ∨ (¬ p19) ∨ (¬ p102) ∨ (¬ p265) ∨ (¬ p576) ∨ (¬ p928) ∨ (¬ p961) ∨ (¬ p1080)) : (¬ p265) ∨ (¬ p15) ∨ (¬ p961) ∨ (¬ p1080) ∨ p918 ∨ p101 ∨ (¬ p576) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18670 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u3)

theorem step27710 (p18 p19 p423 p790 p814 p1141 p1255 p1346 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26893 : p814 ∨ p790)
    (h26829 : p19 ∨ p18)
    (h20535 : (¬ p19) ∨ (¬ p814) ∨ (¬ p1141) ∨ (¬ p1255) ∨ (¬ p1346)) : p423 ∨ (¬ p1346) ∨ p790 ∨ (¬ p1255) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20535 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)

theorem step27711 (p15 p18 p19 p124 p141 p258 p288 p304 p422 p1209 : Prop)
    (h26859 : p304 ∨ p124)
    (h26829 : p19 ∨ p18)
    (h26855 : p288 ∨ p258)
    (h25800 : (¬ p304) ∨ (¬ p15) ∨ (¬ p19) ∨ (¬ p1209) ∨ (¬ p141) ∨ (¬ p422) ∨ (¬ p288)) : p124 ∨ (¬ p422) ∨ (¬ p141) ∨ p18 ∨ (¬ p15) ∨ (¬ p1209) ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h25800 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u9)

theorem step27712 (p18 p19 p303 p329 p387 p438 p1366 : Prop)
    (h26829 : p19 ∨ p18)
    (h26867 : p387 ∨ p303)
    (h16754 : (¬ p19) ∨ (¬ p329) ∨ (¬ p387) ∨ (¬ p438) ∨ (¬ p1366)) : (¬ p1366) ∨ p18 ∨ (¬ p329) ∨ (¬ p438) ∨ p303 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p329 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16754 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)

theorem step27713 (p10 p18 p19 p224 p303 p323 p387 : Prop)
    (h26867 : p387 ∨ p303)
    (h26861 : p323 ∨ p10)
    (h26829 : p19 ∨ p18)
    (h17313 : (¬ p19) ∨ (¬ p224) ∨ (¬ p323) ∨ (¬ p387)) : p303 ∨ (¬ p224) ∨ p10 ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17313 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step27714 (p18 p19 p386 p423 p1141 p1452 p1465 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26829 : p19 ∨ p18)
    (h17678 : (¬ p19) ∨ (¬ p386) ∨ (¬ p1141) ∨ (¬ p1452) ∨ (¬ p1465)) : p423 ∨ (¬ p1452) ∨ (¬ p386) ∨ p18 ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p386 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17678 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)

theorem step27715 (p15 p18 p19 p134 p424 : Prop)
    (h26829 : p19 ∨ p18)
    (h16905 : (¬ p15) ∨ (¬ p19) ∨ (¬ p134) ∨ (¬ p424)) : (¬ p15) ∨ p18 ∨ (¬ p134) ∨ (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16905 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)

theorem step27716 (p3 p18 p19 p68 p134 p225 p226 : Prop)
    (h26829 : p19 ∨ p18)
    (h26847 : p226 ∨ p3)
    (h20379 : (¬ p19) ∨ p68 ∨ (¬ p134) ∨ (¬ p225) ∨ (¬ p226)) : p68 ∨ p18 ∨ (¬ p225) ∨ (¬ p134) ∨ p3 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p68) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20379 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)

theorem step27717 (p3 p18 p19 p38 p134 p168 p226 p1095 p1096 p1115 : Prop)
    (h26829 : p19 ∨ p18)
    (h26847 : p226 ∨ p3)
    (h20440 : (¬ p19) ∨ (¬ p38) ∨ (¬ p134) ∨ (¬ p168) ∨ (¬ p226) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1115)) : (¬ p38) ∨ p18 ∨ (¬ p1115) ∨ (¬ p134) ∨ (¬ p1096) ∨ p3 ∨ (¬ p168) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p168 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20440 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u2)

theorem step27718 (p3 p6 p18 p19 p107 p344 : Prop)
    (h26829 : p19 ∨ p18)
    (h16317 : (¬ p3) ∨ (¬ p6) ∨ (¬ p19) ∨ (¬ p107) ∨ (¬ p344)) : (¬ p3) ∨ (¬ p344) ∨ (¬ p6) ∨ p18 ∨ (¬ p107) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16317 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)

theorem step27719 (p6 p18 p19 p423 p1141 p1465 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26829 : p19 ∨ p18)
    (h18933 : (¬ p6) ∨ (¬ p19) ∨ (¬ p1141) ∨ (¬ p1465)) : p423 ∨ (¬ p1465) ∨ p18 ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18933 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)

theorem step27720 (p6 p18 p19 p419 p996 p1188 p1287 : Prop)
    (h26829 : p19 ∨ p18)
    (h26905 : p996 ∨ p419)
    (h18695 : (¬ p6) ∨ (¬ p19) ∨ (¬ p996) ∨ (¬ p1188) ∨ (¬ p1287)) : (¬ p1188) ∨ p18 ∨ (¬ p1287) ∨ (¬ p6) ∨ p419 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18695 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u2)

theorem step27721 (p6 p18 p19 p38 : Prop)
    (h26829 : p19 ∨ p18)
    (h130 : (¬ p6) ∨ (¬ p19) ∨ (¬ p38)) : (¬ p38) ∨ p18 ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h130 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)

theorem step27722 (p6 p18 p19 p192 p422 p1035 p1256 : Prop)
    (h26929 : p1256 ∨ p422)
    (h26829 : p19 ∨ p18)
    (h17122 : (¬ p6) ∨ (¬ p19) ∨ (¬ p192) ∨ (¬ p1035) ∨ (¬ p1256)) : p422 ∨ (¬ p192) ∨ (¬ p1035) ∨ (¬ p6) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p422) := fun hu => hn (Or.inl hu)
  have u1 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17122 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step27723 (p6 p18 p19 p234 p344 p540 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26829 : p19 ∨ p18)
    (h17362 : (¬ p6) ∨ (¬ p19) ∨ (¬ p344) ∨ (¬ p540) ∨ (¬ p1187)) : p234 ∨ p18 ∨ (¬ p540) ∨ (¬ p344) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17362 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step27724 (p2 p6 p14 p18 p19 p229 p481 : Prop)
    (h26849 : p229 ∨ p14)
    (h26829 : p19 ∨ p18)
    (h26873 : p481 ∨ p2)
    (h17548 : (¬ p6) ∨ (¬ p19) ∨ (¬ p229) ∨ (¬ p481)) : p14 ∨ p18 ∨ p2 ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17548 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)

theorem step27725 (p6 p12 p14 p18 p19 p229 p1036 : Prop)
    (h26849 : p229 ∨ p14)
    (h26907 : p1036 ∨ p12)
    (h26829 : p19 ∨ p18)
    (h18401 : (¬ p6) ∨ (¬ p19) ∨ (¬ p229) ∨ (¬ p1036)) : p14 ∨ p12 ∨ (¬ p6) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18401 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step27726 (p6 p18 p19 p185 p234 p790 p800 p918 p928 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26901 : p928 ∨ p918)
    (h26829 : p19 ∨ p18)
    (h18684 : (¬ p6) ∨ (¬ p19) ∨ (¬ p185) ∨ (¬ p790) ∨ (¬ p800) ∨ (¬ p928) ∨ (¬ p1187)) : (¬ p800) ∨ p234 ∨ (¬ p790) ∨ p918 ∨ p18 ∨ (¬ p185) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p800 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p234) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18684 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u7)

theorem step27727 (p18 p19 p67 p101 p102 p124 p206 p304 : Prop)
    (h26859 : p304 ∨ p124)
    (h26837 : p102 ∨ p101)
    (h26829 : p19 ∨ p18)
    (h18025 : (¬ p19) ∨ (¬ p67) ∨ (¬ p102) ∨ (¬ p206) ∨ (¬ p304)) : p124 ∨ p101 ∨ p18 ∨ (¬ p67) ∨ (¬ p206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18025 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step27728 (p18 p19 p125 p207 p234 p347 p362 p540 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26829 : p19 ∨ p18)
    (h26865 : p362 ∨ p125)
    (h18024 : (¬ p19) ∨ (¬ p207) ∨ (¬ p347) ∨ (¬ p362) ∨ (¬ p540) ∨ (¬ p1187)) : p234 ∨ p18 ∨ (¬ p207) ∨ (¬ p347) ∨ (¬ p540) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18024 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)

theorem step27729 (p3 p18 p19 p38 p224 p225 p226 : Prop)
    (h26847 : p226 ∨ p3)
    (h26829 : p19 ∨ p18)
    (h16533 : (¬ p19) ∨ (¬ p38) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226)) : (¬ p38) ∨ p3 ∨ p18 ∨ (¬ p225) ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16533 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step27730 (p14 p18 p19 p104 p121 p229 p1084 : Prop)
    (h26849 : p229 ∨ p14)
    (h26829 : p19 ∨ p18)
    (h16811 : (¬ p19) ∨ (¬ p104) ∨ (¬ p121) ∨ (¬ p229) ∨ (¬ p1084)) : p14 ∨ p18 ∨ (¬ p1084) ∨ (¬ p121) ∨ (¬ p104) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16811 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)

theorem step27731 (p6 p14 p18 p19 p104 p229 p344 p346 : Prop)
    (h26849 : p229 ∨ p14)
    (h26829 : p19 ∨ p18)
    (h26863 : p346 ∨ p344)
    (h17981 : (¬ p6) ∨ (¬ p19) ∨ (¬ p104) ∨ (¬ p229) ∨ (¬ p346)) : (¬ p104) ∨ p14 ∨ p18 ∨ p344 ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p14) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17981 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)

theorem step27732 (p18 p19 p189 p193 p422 p423 p1141 p1256 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26929 : p1256 ∨ p422)
    (h26845 : p193 ∨ p189)
    (h26829 : p19 ∨ p18)
    (h17246 : (¬ p19) ∨ (¬ p193) ∨ (¬ p1141) ∨ (¬ p1256)) : p423 ∨ p422 ∨ p189 ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17246 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step27733 (p18 p19 p189 p193 p234 p424 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26845 : p193 ∨ p189)
    (h26829 : p19 ∨ p18)
    (h18570 : (¬ p19) ∨ (¬ p193) ∨ (¬ p424) ∨ (¬ p1187)) : p234 ∨ p189 ∨ (¬ p424) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18570 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step27735 (p18 p19 p50 p101 p102 p136 p258 : Prop)
    (h26829 : p19 ∨ p18)
    (h26837 : p102 ∨ p101)
    (h16817 : (¬ p19) ∨ (¬ p50) ∨ (¬ p102) ∨ (¬ p136) ∨ (¬ p258)) : (¬ p258) ∨ (¬ p50) ∨ (¬ p136) ∨ p18 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p50 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p136 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16817 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)

theorem step27736 (p6 p14 p18 p19 p156 p185 p192 p229 p789 p790 : Prop)
    (h26829 : p19 ∨ p18)
    (h26849 : p229 ∨ p14)
    (h19701 : (¬ p6) ∨ (¬ p19) ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p192) ∨ (¬ p229) ∨ (¬ p789) ∨ (¬ p790)) : (¬ p789) ∨ p18 ∨ (¬ p6) ∨ (¬ p192) ∨ p14 ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19701 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u7)

theorem step27738 (p15 p18 p19 p980 p1055 p1103 p1449 p1665 : Prop)
    (h26829 : p19 ∨ p18)
    (h17770 : (¬ p15) ∨ (¬ p19) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1103) ∨ (¬ p1449) ∨ (¬ p1665)) : (¬ p1665) ∨ (¬ p15) ∨ (¬ p1449) ∨ (¬ p980) ∨ (¬ p1055) ∨ p18 ∨ (¬ p1103) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17770 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u0)

theorem step27739 (p2 p6 p18 p19 p424 p481 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26829 : p19 ∨ p18)
    (h26873 : p481 ∨ p2)
    (h18867 : (¬ p6) ∨ (¬ p19) ∨ (¬ p481) ∨ (¬ p796)) : p424 ∨ p18 ∨ p2 ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18867 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)

theorem step27742 (p6 p8 p18 p19 p344 p346 p561 : Prop)
    (h26863 : p346 ∨ p344)
    (h26829 : p19 ∨ p18)
    (h18870 : (¬ p6) ∨ (¬ p8) ∨ (¬ p19) ∨ (¬ p346) ∨ (¬ p561)) : (¬ p561) ∨ p344 ∨ p18 ∨ (¬ p6) ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18870 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step27744 (p10 p15 p18 p19 p303 p323 p387 : Prop)
    (h26867 : p387 ∨ p303)
    (h26829 : p19 ∨ p18)
    (h26861 : p323 ∨ p10)
    (h17860 : (¬ p15) ∨ (¬ p19) ∨ (¬ p323) ∨ (¬ p387)) : (¬ p15) ∨ p303 ∨ p18 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17860 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)

theorem step27745 (p10 p15 p18 p19 p224 p323 p347 p382 p621 p657 : Prop)
    (h26861 : p323 ∨ p10)
    (h26829 : p19 ∨ p18)
    (h26887 : p657 ∨ p224)
    (h20328 : (¬ p15) ∨ (¬ p19) ∨ (¬ p323) ∨ (¬ p347) ∨ (¬ p382) ∨ (¬ p621) ∨ (¬ p657)) : (¬ p15) ∨ (¬ p347) ∨ p10 ∨ p18 ∨ (¬ p621) ∨ (¬ p382) ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p621 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20328 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u9)

theorem step27748 (p44 p234 p424 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h11254 : (¬ p44) ∨ (¬ p234) ∨ (¬ p796)) : (¬ p44) ∨ p424 ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p424) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h11254 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step27749 (p44 p63 p85 p134 p234 p1249 p1330 p1366 p1489 : Prop)
    (h26835 : p85 ∨ p63)
    (h16887 : (¬ p44) ∨ (¬ p85) ∨ (¬ p134) ∨ (¬ p234) ∨ (¬ p1249) ∨ (¬ p1330) ∨ (¬ p1366) ∨ (¬ p1489)) : (¬ p1366) ∨ (¬ p1249) ∨ (¬ p1489) ∨ (¬ p234) ∨ (¬ p44) ∨ p63 ∨ (¬ p134) ∨ (¬ p1330) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h16887 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u2)

theorem step27750 (p44 p63 p85 p134 p234 p382 p406 p431 p476 p1015 p1385 : Prop)
    (h26869 : p406 ∨ p382)
    (h26835 : p85 ∨ p63)
    (h16889 : (¬ p44) ∨ (¬ p85) ∨ (¬ p134) ∨ (¬ p234) ∨ (¬ p406) ∨ (¬ p431) ∨ (¬ p476) ∨ (¬ p1015) ∨ (¬ p1385)) : (¬ p431) ∨ (¬ p1015) ∨ (¬ p44) ∨ (¬ p1385) ∨ (¬ p134) ∨ p382 ∨ (¬ p234) ∨ p63 ∨ (¬ p476) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p476 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h16889 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u3)

theorem step27751 (p15 p44 p89 p189 p193 : Prop)
    (h26845 : p193 ∨ p189)
    (h13949 : p15 ∨ (¬ p44) ∨ (¬ p89) ∨ (¬ p193)) : (¬ p44) ∨ p189 ∨ (¬ p89) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h13949 with q0 | q1 | q2 | q3
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step27752 (p44 p90 p189 p193 p224 p234 p382 p542 p657 p819 p834 p918 : Prop)
    (h26845 : p193 ∨ p189)
    (h26887 : p657 ∨ p224)
    (h26586 : p90)
    (h18664 : (¬ p44) ∨ (¬ p90) ∨ (¬ p193) ∨ (¬ p234) ∨ (¬ p382) ∨ (¬ p542) ∨ (¬ p657) ∨ (¬ p819) ∨ (¬ p834) ∨ (¬ p918)) : (¬ p918) ∨ p189 ∨ (¬ p234) ∨ p224 ∨ (¬ p834) ∨ (¬ p819) ∨ (¬ p382) ∨ (¬ p44) ∨ (¬ p542) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p834 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p819 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p90 := by
    exact h26586
  rcases h18664 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u4)
  · exact False.elim (q9 u0)

theorem step27753 (p18 p19 p44 p189 p193 p382 p713 p897 p1325 p1449 p1665 : Prop)
    (h26845 : p193 ∨ p189)
    (h26829 : p19 ∨ p18)
    (h18675 : (¬ p19) ∨ (¬ p44) ∨ (¬ p193) ∨ (¬ p382) ∨ (¬ p713) ∨ (¬ p897) ∨ (¬ p1325) ∨ (¬ p1449) ∨ (¬ p1665)) : (¬ p1665) ∨ (¬ p897) ∨ (¬ p1325) ∨ p189 ∨ (¬ p44) ∨ (¬ p382) ∨ (¬ p1449) ∨ (¬ p713) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p713 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h18675 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u0)

theorem step27754 (p44 p90 p189 p193 p234 p419 p431 p996 p1015 p1385 : Prop)
    (h26586 : p90)
    (h26905 : p996 ∨ p419)
    (h26845 : p193 ∨ p189)
    (h18805 : (¬ p44) ∨ (¬ p90) ∨ (¬ p193) ∨ (¬ p234) ∨ (¬ p431) ∨ (¬ p996) ∨ (¬ p1015) ∨ (¬ p1385)) : (¬ p44) ∨ (¬ p431) ∨ (¬ p1385) ∨ (¬ p1015) ∨ p419 ∨ (¬ p234) ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p90 := by
    exact h26586
  have u8 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18805 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u2)

theorem step27755 (p14 p44 p163 p167 : Prop)
    (h26843 : p167 ∨ p163)
    (h11337 : (¬ p14) ∨ (¬ p44) ∨ (¬ p167)) : (¬ p44) ∨ (¬ p14) ∨ p163 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p163) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h11337 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)

theorem step27758 (p234 p1187 p1192 : Prop)
    (h26920 : (¬ p234) ∨ (¬ p1187))
    (h20796 : p1192 ∨ p1187) : p1192 ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1192) := fun hu => hn (Or.inl hu)
  have u1 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1187) := by
    rcases h26920 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h20796 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step27759 (p2 p38 p234 p1187 : Prop)
    (h26920 : (¬ p234) ∨ (¬ p1187))
    (h10840 : (¬ p2) ∨ (¬ p38) ∨ p1187) : (¬ p38) ∨ (¬ p234) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1187) := by
    rcases h26920 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h10840 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (u3 q2)

theorem step27760 (p2 p192 p790 p814 : Prop)
    (h26892 : (¬ p790) ∨ (¬ p814))
    (h21388 : p192 ∨ p814 ∨ (¬ p2)) : (¬ p2) ∨ (¬ p790) ∨ p192 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p192) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p814) := by
    rcases h26892 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h21388 with q0 | q1 | q2
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u0)

theorem step27777 (p8 p125 p305 p348 p362 p710 : Prop)
    (h26889 : p710 ∨ p8)
    (h26865 : p362 ∨ p125)
    (h14893 : (¬ p305) ∨ (¬ p348) ∨ (¬ p362) ∨ (¬ p710)) : (¬ p348) ∨ (¬ p305) ∨ p8 ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h14893 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step27778 (p8 p126 p258 p308 p348 p710 : Prop)
    (h26889 : p710 ∨ p8)
    (h20036 : (¬ p126) ∨ (¬ p258) ∨ (¬ p308) ∨ (¬ p348) ∨ (¬ p710)) : (¬ p348) ∨ (¬ p258) ∨ (¬ p308) ∨ p8 ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p308 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20036 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step27780 (p101 p102 p124 p125 p304 p348 p362 p728 : Prop)
    (h26859 : p304 ∨ p124)
    (h26837 : p102 ∨ p101)
    (h26865 : p362 ∨ p125)
    (h18515 : (¬ p102) ∨ (¬ p304) ∨ (¬ p348) ∨ (¬ p362) ∨ (¬ p728)) : (¬ p728) ∨ p124 ∨ (¬ p348) ∨ p101 ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18515 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u0)

theorem step27787 (p101 p102 p106 p116 p117 p118 p119 p120 : Prop)
    (h26836 : (¬ p101) ∨ (¬ p102))
    (h567 : p102 ∨ p106 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : (¬ p119) ∨ (¬ p116) ∨ (¬ p101) ∨ (¬ p120) ∨ (¬ p117) ∨ (¬ p118) ∨ p106 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p119 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p117 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p118 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p106) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p102) := by
    rcases h26836 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h567 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u3)

theorem step27790 (p104 p225 p344 p346 : Prop)
    (h26863 : p346 ∨ p344)
    (h14153 : (¬ p104) ∨ p225 ∨ (¬ p346)) : (¬ p104) ∨ p225 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h14153 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)

theorem step27792 (p1 p110 p344 p346 p690 p713 p1366 : Prop)
    (h26863 : p346 ∨ p344)
    (h18387 : (¬ p1) ∨ (¬ p110) ∨ (¬ p346) ∨ (¬ p690) ∨ (¬ p713) ∨ (¬ p1366)) : (¬ p1366) ∨ (¬ p713) ∨ (¬ p690) ∨ (¬ p1) ∨ p344 ∨ (¬ p110) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p713 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18387 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u0)

theorem step27793 (p1 p3 p41 p187 p224 p419 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h20161 : (¬ p1) ∨ (¬ p3) ∨ (¬ p41) ∨ (¬ p187) ∨ (¬ p224) ∨ (¬ p996)) : p419 ∨ (¬ p3) ∨ (¬ p1) ∨ (¬ p187) ∨ (¬ p41) ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h20161 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)

theorem step27794 (p1 p12 p15 p69 p124 p234 p344 p496 p664 p1036 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26833 : p69 ∨ p15)
    (h26907 : p1036 ∨ p12)
    (h18815 : (¬ p1) ∨ (¬ p69) ∨ (¬ p124) ∨ (¬ p344) ∨ (¬ p496) ∨ (¬ p664) ∨ (¬ p1036) ∨ (¬ p1187)) : p234 ∨ (¬ p1) ∨ (¬ p496) ∨ (¬ p664) ∨ p15 ∨ (¬ p124) ∨ p12 ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18815 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u8)

theorem step27795 (p1 p163 p189 p193 p224 p419 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26845 : p193 ∨ p189)
    (h20163 : (¬ p1) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p224) ∨ (¬ p996)) : p419 ∨ (¬ p1) ∨ (¬ p163) ∨ p189 ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20163 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step27825 (p225 p542 p544 p551 p552 p553 p554 p555 : Prop)
    (h26876 : (¬ p225) ∨ (¬ p544))
    (h3034 : p542 ∨ p544 ∨ (¬ p551) ∨ (¬ p552) ∨ (¬ p553) ∨ (¬ p554) ∨ (¬ p555)) : (¬ p553) ∨ (¬ p552) ∨ (¬ p225) ∨ p542 ∨ (¬ p551) ∨ (¬ p554) ∨ (¬ p555) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p553 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p552 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p542) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p551 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p554 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p555 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p544) := by
    rcases h26876 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h3034 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step27826 (p2 p68 p234 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h14241 : p2 ∨ (¬ p68) ∨ (¬ p1187)) : p234 ∨ (¬ p68) ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p2) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h14241 with q0 | q1 | q2
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step27828 (p10 p39 p63 p68 p101 p102 p125 p211 p362 p897 p1096 p1099 : Prop)
    (h26865 : p362 ∨ p125)
    (h26913 : p1099 ∨ p1096)
    (h26837 : p102 ∨ p101)
    (h17620 : (¬ p10) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p102) ∨ (¬ p211) ∨ (¬ p362) ∨ (¬ p897) ∨ (¬ p1099)) : p125 ∨ (¬ p10) ∨ (¬ p897) ∨ p1096 ∨ p101 ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p211) ∨ (¬ p68) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p125) := fun hu => hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17620 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u10)

theorem step27829 (p10 p14 p68 p105 p125 p211 p229 p362 : Prop)
    (h26865 : p362 ∨ p125)
    (h26849 : p229 ∨ p14)
    (h17540 : (¬ p10) ∨ (¬ p68) ∨ (¬ p105) ∨ (¬ p211) ∨ (¬ p229) ∨ (¬ p362)) : (¬ p10) ∨ p125 ∨ (¬ p211) ∨ p14 ∨ (¬ p105) ∨ (¬ p68) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p125) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17540 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u6)

theorem step27830 (p68 p423 p1140 p1141 : Prop)
    (h26917 : p1141 ∨ p423)
    (h11251 : (¬ p68) ∨ (¬ p1140) ∨ (¬ p1141)) : p423 ∨ (¬ p1140) ∨ (¬ p68) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h11251 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step27832 (p6 p68 p127 p234 p329 p1187 : Prop)
    (h26839 : p127 ∨ p6)
    (h26921 : p1187 ∨ p234)
    (h14434 : (¬ p68) ∨ (¬ p127) ∨ (¬ p329) ∨ (¬ p1187)) : p6 ∨ p234 ∨ (¬ p68) ∨ (¬ p329) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p234) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p329 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h14434 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)

theorem step27834 (p41 p45 p124 p135 p265 p304 p580 p633 : Prop)
    (h26859 : p304 ∨ p124)
    (h26831 : p45 ∨ p41)
    (h20290 : (¬ p45) ∨ (¬ p135) ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p580) ∨ (¬ p633)) : p124 ∨ (¬ p265) ∨ (¬ p580) ∨ (¬ p633) ∨ (¬ p135) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20290 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step27835 (p125 p494 p595 p596 p616 : Prop)
    (h26882 : (¬ p595) ∨ (¬ p616))
    (h14090 : (¬ p125) ∨ (¬ p494) ∨ (¬ p596) ∨ p616) : (¬ p125) ∨ (¬ p596) ∨ (¬ p595) ∨ (¬ p494) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p596 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p616) := by
    rcases h26882 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h14090 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (u4 q3)

theorem step27837 (p124 p304 p389 p423 p455 p456 p494 p633 p1035 p1325 : Prop)
    (h26871 : p456 ∨ p455)
    (h26859 : p304 ∨ p124)
    (h20195 : (¬ p304) ∨ (¬ p389) ∨ (¬ p423) ∨ (¬ p456) ∨ (¬ p494) ∨ (¬ p633) ∨ (¬ p1035) ∨ (¬ p1325)) : p455 ∨ (¬ p389) ∨ (¬ p633) ∨ (¬ p494) ∨ (¬ p1035) ∨ p124 ∨ (¬ p1325) ∨ (¬ p423) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20195 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u6)

theorem step27838 (p86 p124 p304 p389 p455 p456 p494 p633 p789 p790 : Prop)
    (h26859 : p304 ∨ p124)
    (h26871 : p456 ∨ p455)
    (h20251 : (¬ p86) ∨ (¬ p304) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p494) ∨ (¬ p633) ∨ (¬ p789) ∨ (¬ p790)) : (¬ p789) ∨ (¬ p790) ∨ (¬ p389) ∨ (¬ p633) ∨ p124 ∨ (¬ p86) ∨ (¬ p494) ∨ p455 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p455) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20251 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u1)

theorem step27839 (p13 p86 p125 p185 p237 p420 p455 p456 p494 p601 p1115 p1116 : Prop)
    (h26871 : p456 ∨ p455)
    (h26881 : p601 ∨ p420)
    (h26915 : p1116 ∨ p1115)
    (h26851 : p237 ∨ p185)
    (h17329 : (¬ p13) ∨ (¬ p86) ∨ (¬ p125) ∨ (¬ p237) ∨ (¬ p456) ∨ (¬ p494) ∨ (¬ p601) ∨ (¬ p1116)) : p455 ∨ p420 ∨ (¬ p494) ∨ (¬ p13) ∨ p1115 ∨ p185 ∨ (¬ p125) ∨ (¬ p86) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p420) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17329 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u10)

theorem step27840 (p86 p124 p189 p193 p304 p327 p420 p424 p494 p633 : Prop)
    (h26859 : p304 ∨ p124)
    (h26845 : p193 ∨ p189)
    (h18681 : (¬ p86) ∨ (¬ p193) ∨ (¬ p304) ∨ (¬ p327) ∨ (¬ p420) ∨ (¬ p424) ∨ (¬ p494) ∨ (¬ p633)) : (¬ p420) ∨ p124 ∨ (¬ p327) ∨ (¬ p424) ∨ (¬ p633) ∨ (¬ p494) ∨ p189 ∨ (¬ p86) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18681 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u4)

theorem step27847 (p125 p362 p420 p425 p601 : Prop)
    (h26864 : (¬ p125) ∨ (¬ p362))
    (h26881 : p601 ∨ p420)
    (h13656 : p362 ∨ (¬ p425) ∨ (¬ p601)) : (¬ p425) ∨ (¬ p125) ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p362) := by
    rcases h26864 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u4 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h13656 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)

theorem step27848 (p124 p304 p425 p836 p1076 p1115 p1116 : Prop)
    (h26859 : p304 ∨ p124)
    (h26915 : p1116 ∨ p1115)
    (h20449 : (¬ p304) ∨ (¬ p425) ∨ (¬ p836) ∨ (¬ p1076) ∨ (¬ p1116)) : p124 ∨ (¬ p425) ∨ (¬ p836) ∨ (¬ p1076) ∨ p1115 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20449 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)

theorem step27849 (p24 p63 p125 p134 p425 p431 p438 p789 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h20413 : (¬ p24) ∨ (¬ p63) ∨ (¬ p125) ∨ (¬ p134) ∨ (¬ p425) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p789) ∨ (¬ p1393)) : (¬ p431) ∨ (¬ p24) ∨ (¬ p134) ∨ (¬ p425) ∨ (¬ p438) ∨ (¬ p63) ∨ (¬ p125) ∨ p1385 ∨ (¬ p789) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20413 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u9)

theorem step27850 (p8 p63 p85 p305 p425 p431 p582 p595 p710 p734 p1286 : Prop)
    (h26889 : p710 ∨ p8)
    (h26835 : p85 ∨ p63)
    (h16783 : (¬ p85) ∨ (¬ p305) ∨ (¬ p425) ∨ (¬ p431) ∨ (¬ p582) ∨ (¬ p595) ∨ (¬ p710) ∨ (¬ p734) ∨ (¬ p1286)) : (¬ p305) ∨ (¬ p431) ∨ (¬ p425) ∨ (¬ p595) ∨ p8 ∨ (¬ p734) ∨ p63 ∨ (¬ p1286) ∨ (¬ p582) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h16783 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u7)

theorem step27851 (p124 p304 p344 p346 p425 p582 p897 p904 p927 : Prop)
    (h26859 : p304 ∨ p124)
    (h26899 : p904 ∨ p897)
    (h26863 : p346 ∨ p344)
    (h17207 : (¬ p304) ∨ (¬ p346) ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p904) ∨ (¬ p927)) : p124 ∨ (¬ p927) ∨ p897 ∨ p344 ∨ (¬ p582) ∨ (¬ p425) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17207 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u1)

theorem step27852 (p63 p85 p125 p303 p425 p582 p665 p1095 p1096 : Prop)
    (h26835 : p85 ∨ p63)
    (h16558 : (¬ p85) ∨ (¬ p125) ∨ (¬ p303) ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p665) ∨ (¬ p1095) ∨ (¬ p1096)) : (¬ p125) ∨ (¬ p1095) ∨ (¬ p425) ∨ p63 ∨ (¬ p582) ∨ (¬ p665) ∨ (¬ p303) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16558 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u7)

theorem step27853 (p48 p234 p305 p344 p346 p422 p424 p425 p582 p796 p1055 p1076 p1077 p1256 : Prop)
    (h26929 : p1256 ∨ p422)
    (h26911 : p1077 ∨ p1076)
    (h26863 : p346 ∨ p344)
    (h26891 : p796 ∨ p424)
    (h16739 : (¬ p48) ∨ (¬ p234) ∨ (¬ p305) ∨ (¬ p346) ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p796) ∨ (¬ p1055) ∨ (¬ p1077) ∨ (¬ p1256)) : (¬ p425) ∨ (¬ p305) ∨ p422 ∨ (¬ p234) ∨ p1076 ∨ p344 ∨ (¬ p48) ∨ p424 ∨ (¬ p1055) ∨ (¬ p582) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p424) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u12 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u13 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h16739 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u12)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u13)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u11)
  · exact False.elim (q9 u10)

theorem step27854 (p135 p189 p305 p425 p579 p860 p980 p1055 p1325 p1333 p1346 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h20046 : (¬ p135) ∨ (¬ p189) ∨ (¬ p305) ∨ (¬ p425) ∨ (¬ p579) ∨ (¬ p860) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1333) ∨ (¬ p1346)) : (¬ p1346) ∨ (¬ p425) ∨ (¬ p579) ∨ p1325 ∨ (¬ p860) ∨ (¬ p305) ∨ (¬ p1055) ∨ (¬ p980) ∨ (¬ p189) ∨ (¬ p135) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p860 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20046 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u0)

theorem step27860 (p2 p6 p127 p325 p349 p757 p1665 : Prop)
    (h26839 : p127 ∨ p6)
    (h19884 : (¬ p2) ∨ (¬ p127) ∨ (¬ p325) ∨ (¬ p349) ∨ (¬ p757) ∨ (¬ p1665)) : (¬ p325) ∨ (¬ p2) ∨ (¬ p349) ∨ (¬ p1665) ∨ (¬ p757) ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p757 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19884 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step27861 (p2 p125 p211 p325 p362 : Prop)
    (h26865 : p362 ∨ p125)
    (h15798 : (¬ p2) ∨ (¬ p211) ∨ (¬ p325) ∨ (¬ p362)) : (¬ p325) ∨ (¬ p211) ∨ p125 ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h15798 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step27864 (p18 p19 p101 p102 p234 p325 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26829 : p19 ∨ p18)
    (h26837 : p102 ∨ p101)
    (h24167 : (¬ p325) ∨ (¬ p19) ∨ (¬ p1187) ∨ (¬ p102)) : (¬ p325) ∨ p234 ∨ p18 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p234) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h24167 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)

theorem step27865 (p2 p6 p127 p224 p303 p325 p657 : Prop)
    (h26839 : p127 ∨ p6)
    (h26887 : p657 ∨ p224)
    (h18420 : (¬ p2) ∨ (¬ p127) ∨ (¬ p303) ∨ (¬ p325) ∨ (¬ p657)) : (¬ p325) ∨ (¬ p2) ∨ p6 ∨ p224 ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18420 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u6)

theorem step27869 (p101 p102 p134 p142 p325 p424 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26841 : p142 ∨ p134)
    (h26837 : p102 ∨ p101)
    (h24169 : (¬ p325) ∨ (¬ p142) ∨ (¬ p102) ∨ (¬ p796)) : (¬ p325) ∨ p424 ∨ p134 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p424) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h24169 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)

theorem step27871 (p18 p19 p126 p143 p234 p325 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26829 : p19 ∨ p18)
    (h20493 : (¬ p19) ∨ (¬ p126) ∨ (¬ p143) ∨ (¬ p325) ∨ (¬ p1187)) : (¬ p325) ∨ p234 ∨ (¬ p126) ∨ p18 ∨ (¬ p143) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p234) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20493 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step27872 (p424 p796 p801 : Prop)
    (h26890 : (¬ p424) ∨ (¬ p796))
    (h20729 : p796 ∨ p801) : (¬ p424) ∨ p801 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p801) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p796) := by
    rcases h26890 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h20729 with q0 | q1
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)

theorem step27876 (p2 p192 p424 p796 : Prop)
    (h26890 : (¬ p424) ∨ (¬ p796))
    (h11962 : (¬ p2) ∨ (¬ p192) ∨ p796) : (¬ p2) ∨ (¬ p192) ∨ (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p796) := by
    rcases h26890 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h11962 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u3 q2)

theorem step27877 (p163 p167 p424 p539 p796 : Prop)
    (h26843 : p167 ∨ p163)
    (h26890 : (¬ p424) ∨ (¬ p796))
    (h13866 : (¬ p167) ∨ (¬ p539) ∨ p796) : (¬ p539) ∨ p163 ∨ (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p539 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u4 : (¬ p796) := by
    rcases h26890 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h13866 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (u4 q2)

#print axioms step27877

end NineRUPTrial
