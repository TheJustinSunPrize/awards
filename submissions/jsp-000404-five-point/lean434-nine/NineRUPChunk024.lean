import Mathlib.Tactic.Tauto

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineRUPTrial

theorem step32631 (p18 p47 p87 p101 p125 p189 p262 p350 p362 p576 p581 : Prop)
    (h26879 : p581 ∨ p576)
    (h26865 : p362 ∨ p125)
    (h19822 : (¬ p18) ∨ (¬ p47) ∨ (¬ p87) ∨ (¬ p101) ∨ (¬ p189) ∨ (¬ p262) ∨ (¬ p350) ∨ (¬ p362) ∨ (¬ p581)) : (¬ p101) ∨ p576 ∨ (¬ p189) ∨ (¬ p350) ∨ p125 ∨ (¬ p18) ∨ (¬ p87) ∨ (¬ p47) ∨ (¬ p262) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19822 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u9)

theorem step32633 (p41 p138 p262 p310 p922 p1055 p1061 p1074 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h18306 : (¬ p41) ∨ (¬ p138) ∨ (¬ p262) ∨ (¬ p310) ∨ (¬ p922) ∨ (¬ p1061) ∨ (¬ p1074)) : p1055 ∨ (¬ p310) ∨ (¬ p262) ∨ (¬ p138) ∨ (¬ p41) ∨ (¬ p1074) ∨ (¬ p922) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1055) := fun hu => hn (Or.inl hu)
  have u1 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p922 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18306 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u5)

theorem step32656 (p420 p597 p601 p604 p605 p606 p607 p608 : Prop)
    (h26880 : (¬ p420) ∨ (¬ p601))
    (h3372 : p597 ∨ p601 ∨ (¬ p604) ∨ (¬ p605) ∨ (¬ p606) ∨ (¬ p607) ∨ (¬ p608)) : p597 ∨ (¬ p608) ∨ (¬ p420) ∨ (¬ p606) ∨ (¬ p604) ∨ (¬ p607) ∨ (¬ p605) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p597) := fun hu => hn (Or.inl hu)
  have u1 : p608 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p606 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p604 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p607 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p605 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p601) := by
    rcases h26880 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h3372 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u1)

theorem step32681 (p521 p789 p858 : Prop)
    (h26897 : p858 ∨ p789)
    (h19614 : p521 ∨ (¬ p858)) : p521 ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p521) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p789) := fun hu => hn (Or.inr hu)
  have u2 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19614 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)

theorem step32682 (p789 p858 p1286 p1388 : Prop)
    (h26897 : p858 ∨ p789)
    (h14085 : (¬ p858) ∨ (¬ p1286) ∨ (¬ p1388)) : (¬ p1286) ∨ (¬ p1388) ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1388 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h14085 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)

theorem step32683 (p189 p382 p406 p789 p820 p858 : Prop)
    (h26869 : p406 ∨ p382)
    (h26897 : p858 ∨ p789)
    (h26197 : (¬ p820) ∨ (¬ p858) ∨ (¬ p189) ∨ (¬ p406)) : p382 ∨ (¬ p189) ∨ (¬ p820) ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p820 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h26197 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step32685 (p234 p435 p789 p858 p1022 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26897 : p858 ∨ p789)
    (h19873 : (¬ p435) ∨ (¬ p858) ∨ (¬ p1022) ∨ (¬ p1187)) : p234 ∨ p789 ∨ (¬ p435) ∨ (¬ p1022) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p789) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19873 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step32686 (p382 p406 p789 p816 p858 : Prop)
    (h26869 : p406 ∨ p382)
    (h26897 : p858 ∨ p789)
    (h5052 : (¬ p406) ∨ (¬ p816) ∨ (¬ p858)) : p382 ∨ (¬ p816) ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h5052 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)

theorem step32687 (p789 p858 p1287 p1388 : Prop)
    (h26897 : p858 ∨ p789)
    (h14668 : (¬ p858) ∨ p1287 ∨ (¬ p1388)) : p1287 ∨ (¬ p1388) ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1287) := fun hu => hn (Or.inl hu)
  have u1 : p1388 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h14668 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)

theorem step32689 (p789 p858 p864 p870 p871 p872 p873 p874 : Prop)
    (h26896 : (¬ p789) ∨ (¬ p858))
    (h4966 : p858 ∨ p864 ∨ (¬ p870) ∨ (¬ p871) ∨ (¬ p872) ∨ (¬ p873) ∨ (¬ p874)) : (¬ p874) ∨ (¬ p870) ∨ (¬ p789) ∨ p864 ∨ (¬ p871) ∨ (¬ p872) ∨ (¬ p873) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p874 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p870 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p864) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p871 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p872 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p873 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p858) := by
    rcases h26896 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h4966 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u0)

theorem step32691 (p5 p6 p9 p10 p41 p303 p922 p1055 p1061 p1074 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h18358 : (¬ p5) ∨ (¬ p6) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p41) ∨ (¬ p303) ∨ (¬ p922) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p9) ∨ (¬ p10) ∨ (¬ p41) ∨ (¬ p6) ∨ p1055 ∨ (¬ p922) ∨ (¬ p5) ∨ (¬ p1074) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p922 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18358 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u7)

theorem step32693 (p5 p6 p10 p41 p89 p185 p237 p303 p918 : Prop)
    (h26851 : p237 ∨ p185)
    (h20352 : (¬ p5) ∨ (¬ p6) ∨ (¬ p10) ∨ (¬ p41) ∨ (¬ p89) ∨ (¬ p237) ∨ (¬ p303) ∨ (¬ p918)) : p185 ∨ (¬ p918) ∨ (¬ p41) ∨ (¬ p10) ∨ (¬ p6) ∨ (¬ p89) ∨ (¬ p5) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h20352 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u1)

theorem step32694 (p6 p126 p140 p191 p301 p303 p424 p476 p687 : Prop)
    (h26857 : p301 ∨ p126)
    (h26200 : (¬ p687) ∨ (¬ p301) ∨ (¬ p424) ∨ (¬ p303) ∨ (¬ p6) ∨ (¬ p476) ∨ (¬ p191) ∨ (¬ p140)) : (¬ p476) ∨ (¬ p687) ∨ (¬ p424) ∨ (¬ p6) ∨ (¬ p191) ∨ p126 ∨ (¬ p303) ∨ (¬ p140) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p476 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p126) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26200 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step32701 (p303 p387 p438 p595 p1542 : Prop)
    (h26867 : p387 ∨ p303)
    (h17496 : (¬ p387) ∨ (¬ p438) ∨ (¬ p595) ∨ (¬ p1542)) : (¬ p1542) ∨ (¬ p595) ∨ p303 ∨ (¬ p438) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17496 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)

theorem step32703 (p63 p438 p1022 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h18579 : (¬ p63) ∨ (¬ p438) ∨ (¬ p1022) ∨ (¬ p1393)) : (¬ p1022) ∨ p1385 ∨ (¬ p63) ∨ (¬ p438) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18579 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step32704 (p303 p387 p419 p424 p438 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26867 : p387 ∨ p303)
    (h17014 : (¬ p387) ∨ (¬ p419) ∨ (¬ p438) ∨ (¬ p796)) : (¬ p438) ∨ p424 ∨ p303 ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p424) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17014 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step32706 (p331 p424 p438 p796 p1371 p1713 : Prop)
    (h26891 : p796 ∨ p424)
    (h18175 : (¬ p331) ∨ (¬ p438) ∨ (¬ p796) ∨ (¬ p1371) ∨ (¬ p1713)) : (¬ p1713) ∨ (¬ p1371) ∨ p424 ∨ (¬ p331) ∨ (¬ p438) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1713 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1371 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p424) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18175 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step32709 (p6 p24 p64 p420 p438 p980 p983 p1055 p1061 p1335 : Prop)
    (h26903 : p983 ∨ p980)
    (h26909 : p1061 ∨ p1055)
    (h22793 : (¬ p64) ∨ (¬ p420) ∨ (¬ p6) ∨ (¬ p983) ∨ (¬ p24) ∨ (¬ p1061) ∨ (¬ p438) ∨ (¬ p1335)) : (¬ p420) ∨ p980 ∨ (¬ p64) ∨ (¬ p6) ∨ (¬ p1335) ∨ (¬ p24) ∨ (¬ p438) ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h22793 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u4)

theorem step32710 (p125 p163 p167 p195 p310 p438 p560 p1035 p1140 p1335 : Prop)
    (h26843 : p167 ∨ p163)
    (h18576 : (¬ p125) ∨ (¬ p167) ∨ (¬ p195) ∨ (¬ p310) ∨ (¬ p438) ∨ (¬ p560) ∨ (¬ p1035) ∨ (¬ p1140) ∨ (¬ p1335)) : (¬ p560) ∨ (¬ p310) ∨ (¬ p1035) ∨ (¬ p125) ∨ (¬ p195) ∨ (¬ p438) ∨ p163 ∨ (¬ p1335) ∨ (¬ p1140) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18576 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u7)

theorem step32711 (p382 p477 p1001 p1140 p1159 : Prop)
    (h26918 : (¬ p1140) ∨ (¬ p1159))
    (h14319 : (¬ p382) ∨ (¬ p477) ∨ (¬ p1001) ∨ p1159) : (¬ p1001) ∨ (¬ p477) ∨ (¬ p1140) ∨ (¬ p382) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1001 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p477 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p1159) := by
    rcases h26918 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h14319 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (u4 q3)

theorem step32714 (p124 p136 p207 p258 p422 p1213 p1256 : Prop)
    (h26929 : p1256 ∨ p422)
    (h16569 : (¬ p124) ∨ (¬ p136) ∨ (¬ p207) ∨ (¬ p258) ∨ (¬ p1213) ∨ (¬ p1256)) : (¬ p258) ∨ p422 ∨ (¬ p207) ∨ (¬ p136) ∨ (¬ p124) ∨ (¬ p1213) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p136 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16569 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)

theorem step32715 (p134 p142 p207 p310 p980 p983 p1055 p1061 p1325 : Prop)
    (h26903 : p983 ∨ p980)
    (h26841 : p142 ∨ p134)
    (h26909 : p1061 ∨ p1055)
    (h17561 : (¬ p142) ∨ (¬ p207) ∨ (¬ p310) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1325)) : p980 ∨ (¬ p310) ∨ (¬ p207) ∨ (¬ p1325) ∨ p134 ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u8 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17561 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u3)

theorem step32716 (p14 p20 p109 p207 p227 p455 p456 : Prop)
    (h26871 : p456 ∨ p455)
    (h19863 : (¬ p14) ∨ (¬ p20) ∨ (¬ p109) ∨ (¬ p207) ∨ (¬ p227) ∨ (¬ p456)) : p455 ∨ (¬ p227) ∨ (¬ p20) ∨ (¬ p14) ∨ (¬ p207) ∨ (¬ p109) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p20 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19863 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)

theorem step32722 (p419 p790 p814 p1015 p1366 : Prop)
    (h26893 : p814 ∨ p790)
    (h17521 : (¬ p419) ∨ (¬ p814) ∨ (¬ p1015) ∨ (¬ p1366)) : (¬ p1366) ∨ (¬ p1015) ∨ (¬ p419) ∨ p790 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17521 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)

theorem step32724 (p2 p6 p127 p303 p387 p419 : Prop)
    (h26839 : p127 ∨ p6)
    (h26867 : p387 ∨ p303)
    (h18693 : (¬ p2) ∨ (¬ p127) ∨ (¬ p387) ∨ (¬ p419)) : (¬ p2) ∨ p6 ∨ p303 ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18693 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)

theorem step32726 (p41 p45 p382 p406 p419 p816 p1385 p1393 : Prop)
    (h26869 : p406 ∨ p382)
    (h26933 : p1393 ∨ p1385)
    (h26831 : p45 ∨ p41)
    (h17808 : (¬ p45) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p816) ∨ (¬ p1393)) : p382 ∨ p1385 ∨ (¬ p419) ∨ (¬ p816) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17808 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)

theorem step32727 (p106 p344 p382 p406 p419 p539 p656 : Prop)
    (h26869 : p406 ∨ p382)
    (h16195 : (¬ p106) ∨ (¬ p344) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p539) ∨ (¬ p656)) : p382 ∨ (¬ p344) ∨ (¬ p656) ∨ (¬ p106) ∨ (¬ p539) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p656 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p539 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16195 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)

theorem step32728 (p224 p419 p539 p657 p886 p897 p904 : Prop)
    (h26899 : p904 ∨ p897)
    (h26887 : p657 ∨ p224)
    (h17108 : (¬ p419) ∨ (¬ p539) ∨ (¬ p657) ∨ (¬ p886) ∨ (¬ p904)) : p897 ∨ p224 ∨ (¬ p886) ∨ (¬ p539) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p897) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p886 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p539 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17108 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step32730 (p2 p6 p127 p419 p1325 : Prop)
    (h26839 : p127 ∨ p6)
    (h18333 : (¬ p2) ∨ (¬ p127) ∨ (¬ p419) ∨ (¬ p1325)) : (¬ p2) ∨ p6 ∨ (¬ p1325) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18333 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)

theorem step32731 (p63 p85 p419 p595 p1286 : Prop)
    (h26835 : p85 ∨ p63)
    (h16401 : (¬ p85) ∨ (¬ p419) ∨ (¬ p595) ∨ (¬ p1286)) : (¬ p1286) ∨ (¬ p595) ∨ (¬ p419) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16401 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)

theorem step32732 (p15 p69 p86 p185 p234 p237 p419 p665 p1115 p1116 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26915 : p1116 ∨ p1115)
    (h26851 : p237 ∨ p185)
    (h26833 : p69 ∨ p15)
    (h18726 : (¬ p69) ∨ (¬ p86) ∨ (¬ p237) ∨ (¬ p419) ∨ (¬ p665) ∨ (¬ p1116) ∨ (¬ p1187)) : p234 ∨ p1115 ∨ (¬ p86) ∨ p185 ∨ (¬ p665) ∨ p15 ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1115) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18726 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u7)

theorem step32735 (p101 p224 p329 p657 p734 p1366 : Prop)
    (h26887 : p657 ∨ p224)
    (h18474 : (¬ p101) ∨ (¬ p329) ∨ (¬ p657) ∨ (¬ p734) ∨ (¬ p1366)) : (¬ p101) ∨ (¬ p1366) ∨ (¬ p329) ∨ p224 ∨ (¬ p734) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p329 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18474 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)

theorem step32739 (p10 p39 p68 p121 p211 p227 p323 p619 p690 p789 p858 p1022 p1206 p1387 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26861 : p323 ∨ p10)
    (h26897 : p858 ∨ p789)
    (h19611 : (¬ p39) ∨ (¬ p68) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p323) ∨ (¬ p619) ∨ (¬ p690) ∨ (¬ p858) ∨ (¬ p1022) ∨ (¬ p1206) ∨ (¬ p1387)) : (¬ p1022) ∨ p121 ∨ (¬ p1387) ∨ (¬ p68) ∨ (¬ p690) ∨ p10 ∨ (¬ p619) ∨ (¬ p227) ∨ (¬ p211) ∨ p789 ∨ (¬ p39) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p619 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u12 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u13 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h19611 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u12)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u13)
  · exact False.elim (q8 u0)
  · exact False.elim (q9 u11)
  · exact False.elim (q10 u2)

theorem step32741 (p18 p124 p161 p210 p304 p1076 p1225 p1229 p1325 : Prop)
    (h26925 : p1225 ∨ p161)
    (h26859 : p304 ∨ p124)
    (h26203 : (¬ p1225) ∨ (¬ p1325) ∨ (¬ p210) ∨ (¬ p1229) ∨ (¬ p18) ∨ (¬ p1076) ∨ (¬ p304)) : p161 ∨ p124 ∨ (¬ p1325) ∨ (¬ p1229) ∨ (¬ p210) ∨ (¬ p1076) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p161) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h26203 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u8)

theorem step32743 (p63 p85 p1229 p1272 p1325 p1508 : Prop)
    (h26835 : p85 ∨ p63)
    (h16604 : (¬ p85) ∨ (¬ p1229) ∨ (¬ p1272) ∨ (¬ p1325) ∨ (¬ p1508)) : (¬ p1229) ∨ (¬ p1272) ∨ (¬ p1325) ∨ (¬ p1508) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1272 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16604 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)

theorem step32744 (p41 p45 p63 p85 p1229 p1257 p1272 : Prop)
    (h26835 : p85 ∨ p63)
    (h26831 : p45 ∨ p41)
    (h16653 : (¬ p45) ∨ (¬ p85) ∨ (¬ p1229) ∨ (¬ p1257) ∨ (¬ p1272)) : (¬ p1257) ∨ (¬ p1229) ∨ p63 ∨ (¬ p1272) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1257 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1272 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16653 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)

theorem step32748 (p63 p85 p425 p532 p582 p961 p1229 p1291 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26835 : p85 ∨ p63)
    (h16784 : (¬ p85) ∨ (¬ p425) ∨ (¬ p532) ∨ (¬ p582) ∨ (¬ p961) ∨ (¬ p1229) ∨ (¬ p1291) ∨ (¬ p1333)) : (¬ p532) ∨ p1325 ∨ (¬ p425) ∨ (¬ p582) ∨ p63 ∨ (¬ p1291) ∨ (¬ p961) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1291 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16784 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u8)

theorem step32772 (p1096 p1099 p1102 : Prop)
    (h26912 : (¬ p1096) ∨ (¬ p1099))
    (h21293 : p1102 ∨ p1099) : p1102 ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1102) := fun hu => hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1099) := by
    rcases h26912 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h21293 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step32780 (p161 p595 p1229 p1232 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26927 : p1232 ∨ p1229)
    (h18270 : (¬ p161) ∨ (¬ p595) ∨ (¬ p1232) ∨ (¬ p1333)) : p1325 ∨ (¬ p161) ∨ p1229 ∨ (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18270 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step32781 (p595 p1074 p1076 p1077 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26911 : p1077 ∨ p1076)
    (h19344 : (¬ p595) ∨ (¬ p1074) ∨ (¬ p1077) ∨ (¬ p1099)) : p1096 ∨ (¬ p1074) ∨ p1076 ∨ (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1096) := fun hu => hn (Or.inl hu)
  have u1 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19344 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step32783 (p63 p85 p595 p929 p980 p1074 p1330 p1542 : Prop)
    (h26835 : p85 ∨ p63)
    (h20374 : (¬ p85) ∨ (¬ p595) ∨ (¬ p929) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1330) ∨ (¬ p1542)) : (¬ p1542) ∨ (¬ p929) ∨ (¬ p980) ∨ p63 ∨ (¬ p1074) ∨ (¬ p595) ∨ (¬ p1330) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20374 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u0)

theorem step32784 (p126 p301 p495 p583 p595 p596 : Prop)
    (h26857 : p301 ∨ p126)
    (h16189 : (¬ p301) ∨ (¬ p495) ∨ (¬ p583) ∨ (¬ p595) ∨ (¬ p596)) : p126 ∨ (¬ p596) ∨ (¬ p595) ∨ (¬ p583) ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p596 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p583 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16189 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u1)

theorem step32786 (p3 p14 p48 p64 p226 p595 p1394 : Prop)
    (h26847 : p226 ∨ p3)
    (h16816 : (¬ p14) ∨ (¬ p48) ∨ (¬ p64) ∨ (¬ p226) ∨ (¬ p595) ∨ (¬ p1394)) : p3 ∨ (¬ p1394) ∨ (¬ p48) ∨ (¬ p595) ∨ (¬ p14) ∨ (¬ p64) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p1394 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16816 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u1)

theorem step32787 (p39 p68 p211 p227 p595 p980 p1229 p1232 p1313 p1387 p1452 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h19612 : (¬ p39) ∨ (¬ p68) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p595) ∨ (¬ p980) ∨ (¬ p1232) ∨ (¬ p1313) ∨ (¬ p1387) ∨ (¬ p1452)) : p1229 ∨ (¬ p1452) ∨ (¬ p595) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p980) ∨ (¬ p1313) ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p1387) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1229) := fun hu => hn (Or.inl hu)
  have u1 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1313 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19612 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u9)
  · exact False.elim (q9 u1)

theorem step32788 (p224 p595 p657 p734 p1542 : Prop)
    (h26887 : p657 ∨ p224)
    (h20628 : (¬ p595) ∨ (¬ p657) ∨ (¬ p734) ∨ (¬ p1542)) : (¬ p1542) ∨ (¬ p734) ∨ p224 ∨ (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20628 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)

theorem step32789 (p8 p63 p85 p431 p595 p710 p734 p929 p1102 p1286 : Prop)
    (h26835 : p85 ∨ p63)
    (h26889 : p710 ∨ p8)
    (h16760 : (¬ p85) ∨ (¬ p431) ∨ (¬ p595) ∨ (¬ p710) ∨ (¬ p734) ∨ (¬ p929) ∨ (¬ p1102) ∨ (¬ p1286)) : (¬ p1102) ∨ (¬ p1286) ∨ p63 ∨ p8 ∨ (¬ p734) ∨ (¬ p595) ∨ (¬ p929) ∨ (¬ p431) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16760 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u1)

theorem step32790 (p17 p84 p256 p258 p288 p595 p1076 p1077 p1229 p1232 p1313 p1394 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h26853 : p256 ∨ p17)
    (h26911 : p1077 ∨ p1076)
    (h26855 : p288 ∨ p258)
    (h16939 : (¬ p84) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p595) ∨ (¬ p1077) ∨ (¬ p1232) ∨ (¬ p1313) ∨ (¬ p1394)) : p1229 ∨ (¬ p1394) ∨ p17 ∨ p1076 ∨ p258 ∨ (¬ p595) ∨ (¬ p1313) ∨ (¬ p84) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1229) := fun hu => hn (Or.inl hu)
  have u1 : p1394 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1313 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16939 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u1)

theorem step32792 (p532 p595 p961 p980 p983 p1286 : Prop)
    (h26903 : p983 ∨ p980)
    (h26206 : (¬ p983) ∨ (¬ p1286) ∨ (¬ p532) ∨ (¬ p961) ∨ (¬ p595)) : p980 ∨ (¬ p961) ∨ (¬ p595) ∨ (¬ p1286) ∨ (¬ p532) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h26206 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)

theorem step32802 (p11 p126 p301 p366 p382 p383 p1443 : Prop)
    (h26857 : p301 ∨ p126)
    (h26935 : p1443 ∨ p11)
    (h19632 : (¬ p301) ∨ (¬ p366) ∨ (¬ p382) ∨ (¬ p383) ∨ (¬ p1443)) : p126 ∨ (¬ p366) ∨ (¬ p383) ∨ (¬ p382) ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p383 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19632 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)

theorem step32824 (p285 p344 p382 p406 p656 p789 p834 p858 : Prop)
    (h26869 : p406 ∨ p382)
    (h26897 : p858 ∨ p789)
    (h19715 : (¬ p285) ∨ (¬ p344) ∨ (¬ p406) ∨ (¬ p656) ∨ (¬ p834) ∨ (¬ p858)) : p382 ∨ (¬ p834) ∨ (¬ p285) ∨ p789 ∨ (¬ p344) ∨ (¬ p656) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p834 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p285 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p656 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19715 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u7)

theorem step32825 (p168 p225 p382 p406 p544 p656 p789 p834 p858 : Prop)
    (h26869 : p406 ∨ p382)
    (h26877 : p544 ∨ p225)
    (h26897 : p858 ∨ p789)
    (h20608 : (¬ p168) ∨ (¬ p406) ∨ (¬ p544) ∨ (¬ p656) ∨ (¬ p834) ∨ (¬ p858)) : p382 ∨ (¬ p834) ∨ p225 ∨ p789 ∨ (¬ p656) ∨ (¬ p168) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p834 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p656 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p168 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20608 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u8)

theorem step32829 (p41 p45 p135 p265 p455 p580 p961 : Prop)
    (h26831 : p45 ∨ p41)
    (h20175 : (¬ p45) ∨ (¬ p135) ∨ (¬ p265) ∨ (¬ p455) ∨ (¬ p580) ∨ (¬ p961)) : (¬ p961) ∨ (¬ p265) ∨ p41 ∨ (¬ p455) ∨ (¬ p580) ∨ (¬ p135) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20175 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u0)

theorem step32830 (p17 p86 p126 p224 p256 p347 p595 p616 p657 p1287 : Prop)
    (h26853 : p256 ∨ p17)
    (h26883 : p616 ∨ p595)
    (h26887 : p657 ∨ p224)
    (h18864 : (¬ p86) ∨ (¬ p126) ∨ (¬ p256) ∨ (¬ p347) ∨ (¬ p616) ∨ (¬ p657) ∨ (¬ p1287)) : (¬ p347) ∨ p17 ∨ p595 ∨ (¬ p86) ∨ (¬ p1287) ∨ (¬ p126) ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18864 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u4)

theorem step32831 (p63 p303 p387 p595 p616 p1287 : Prop)
    (h26867 : p387 ∨ p303)
    (h26883 : p616 ∨ p595)
    (h19593 : (¬ p63) ∨ (¬ p387) ∨ (¬ p616) ∨ (¬ p1287)) : p303 ∨ p595 ∨ (¬ p1287) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19593 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)

theorem step32832 (p11 p86 p124 p228 p258 p266 p595 p616 p1287 p1443 : Prop)
    (h26883 : p616 ∨ p595)
    (h26935 : p1443 ∨ p11)
    (h16588 : (¬ p86) ∨ (¬ p124) ∨ (¬ p228) ∨ (¬ p258) ∨ (¬ p266) ∨ (¬ p616) ∨ (¬ p1287) ∨ (¬ p1443)) : (¬ p258) ∨ p595 ∨ (¬ p228) ∨ (¬ p124) ∨ (¬ p266) ∨ (¬ p1287) ∨ (¬ p86) ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h16588 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u9)

theorem step32833 (p8 p17 p86 p256 p710 p902 p1097 p1287 p1325 p1449 p1651 : Prop)
    (h26853 : p256 ∨ p17)
    (h26889 : p710 ∨ p8)
    (h17126 : (¬ p86) ∨ (¬ p256) ∨ (¬ p710) ∨ (¬ p902) ∨ (¬ p1097) ∨ (¬ p1287) ∨ (¬ p1325) ∨ (¬ p1449) ∨ (¬ p1651)) : (¬ p1651) ∨ p17 ∨ (¬ p1097) ∨ p8 ∨ (¬ p1325) ∨ (¬ p1449) ∨ (¬ p902) ∨ (¬ p86) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1651 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1097 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p902 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17126 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u0)

theorem step32834 (p86 p185 p237 p595 p616 p1076 p1115 p1116 p1287 p1325 : Prop)
    (h26851 : p237 ∨ p185)
    (h26915 : p1116 ∨ p1115)
    (h26883 : p616 ∨ p595)
    (h17411 : (¬ p86) ∨ (¬ p237) ∨ (¬ p616) ∨ (¬ p1076) ∨ (¬ p1116) ∨ (¬ p1287) ∨ (¬ p1325)) : p185 ∨ p1115 ∨ (¬ p1287) ∨ p595 ∨ (¬ p86) ∨ (¬ p1076) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1115) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17411 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u6)

theorem step32835 (p86 p185 p237 p303 p351 p387 p595 p616 p836 p840 p1287 : Prop)
    (h26867 : p387 ∨ p303)
    (h26851 : p237 ∨ p185)
    (h26883 : p616 ∨ p595)
    (h26895 : p840 ∨ p836)
    (h17323 : (¬ p86) ∨ (¬ p237) ∨ (¬ p351) ∨ (¬ p387) ∨ (¬ p616) ∨ (¬ p840) ∨ (¬ p1287)) : p303 ∨ (¬ p351) ∨ p185 ∨ (¬ p1287) ∨ (¬ p86) ∨ p595 ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17323 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u3)

theorem step32836 (p86 p734 p897 p1096 p1099 p1335 p1346 p1508 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h16915 : (¬ p86) ∨ (¬ p734) ∨ (¬ p897) ∨ (¬ p1099) ∨ (¬ p1335) ∨ (¬ p1346) ∨ (¬ p1508)) : (¬ p1346) ∨ (¬ p1508) ∨ (¬ p734) ∨ (¬ p86) ∨ p1096 ∨ (¬ p1335) ∨ (¬ p897) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16915 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u1)

theorem step32837 (p41 p45 p382 p406 p431 p734 p816 p897 p1096 p1099 p1385 p1393 : Prop)
    (h26869 : p406 ∨ p382)
    (h26913 : p1099 ∨ p1096)
    (h26933 : p1393 ∨ p1385)
    (h26831 : p45 ∨ p41)
    (h20238 : (¬ p45) ∨ (¬ p406) ∨ (¬ p431) ∨ (¬ p734) ∨ (¬ p816) ∨ (¬ p897) ∨ (¬ p1099) ∨ (¬ p1393)) : p382 ∨ (¬ p734) ∨ p1096 ∨ (¬ p431) ∨ p1385 ∨ (¬ p897) ∨ (¬ p816) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20238 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u11)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u10)

theorem step32838 (p1 p110 p224 p495 p499 p640 p657 p734 p1076 p1095 p1366 : Prop)
    (h26887 : p657 ∨ p224)
    (h26875 : p499 ∨ p495)
    (h17493 : (¬ p1) ∨ (¬ p110) ∨ (¬ p499) ∨ (¬ p640) ∨ (¬ p657) ∨ (¬ p734) ∨ (¬ p1076) ∨ (¬ p1095) ∨ (¬ p1366)) : (¬ p1366) ∨ (¬ p1) ∨ p224 ∨ p495 ∨ (¬ p110) ∨ (¬ p1076) ∨ (¬ p734) ∨ (¬ p640) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p640 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17493 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u0)

theorem step32839 (p8 p163 p167 p195 p560 p710 p734 p1035 p1140 p1335 : Prop)
    (h26843 : p167 ∨ p163)
    (h26889 : p710 ∨ p8)
    (h18582 : (¬ p167) ∨ (¬ p195) ∨ (¬ p560) ∨ (¬ p710) ∨ (¬ p734) ∨ (¬ p1035) ∨ (¬ p1140) ∨ (¬ p1335)) : p163 ∨ (¬ p1140) ∨ (¬ p1035) ∨ p8 ∨ (¬ p734) ∨ (¬ p560) ∨ (¬ p195) ∨ (¬ p1335) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p163) := fun hu => hn (Or.inl hu)
  have u1 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18582 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u7)

theorem step32840 (p18 p124 p210 p304 p344 p346 p734 : Prop)
    (h26859 : p304 ∨ p124)
    (h26863 : p346 ∨ p344)
    (h20128 : (¬ p18) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p734)) : (¬ p210) ∨ p124 ∨ (¬ p18) ∨ (¬ p734) ∨ p344 := by
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
  have u3 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20128 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)

theorem step32842 (p63 p163 p167 p225 p734 p1273 p1335 p1508 : Prop)
    (h26843 : p167 ∨ p163)
    (h18590 : (¬ p63) ∨ (¬ p167) ∨ (¬ p225) ∨ (¬ p734) ∨ (¬ p1273) ∨ (¬ p1335) ∨ (¬ p1508)) : p163 ∨ (¬ p225) ∨ (¬ p734) ∨ (¬ p63) ∨ (¬ p1273) ∨ (¬ p1508) ∨ (¬ p1335) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p163) := fun hu => hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18590 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u5)

theorem step32843 (p5 p6 p13 p89 p121 p980 p1206 p1346 p1508 : Prop)
    (h26923 : p1206 ∨ p121)
    (h18341 : (¬ p5) ∨ (¬ p6) ∨ (¬ p13) ∨ (¬ p89) ∨ (¬ p980) ∨ (¬ p1206) ∨ (¬ p1346) ∨ (¬ p1508)) : (¬ p1508) ∨ p121 ∨ (¬ p6) ∨ (¬ p13) ∨ (¬ p5) ∨ (¬ p1346) ∨ (¬ p89) ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18341 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u0)

theorem step32844 (p15 p39 p69 p89 p1249 p1346 : Prop)
    (h26833 : p69 ∨ p15)
    (h20230 : (¬ p39) ∨ (¬ p69) ∨ (¬ p89) ∨ (¬ p1249) ∨ (¬ p1346)) : (¬ p1346) ∨ p15 ∨ (¬ p39) ∨ (¬ p1249) ∨ (¬ p89) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20230 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)

theorem step32847 (p15 p69 p310 p344 p423 p496 p536 p726 p1141 p1465 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26833 : p69 ∨ p15)
    (h19770 : (¬ p69) ∨ (¬ p310) ∨ (¬ p344) ∨ (¬ p496) ∨ (¬ p536) ∨ (¬ p726) ∨ (¬ p1141) ∨ (¬ p1465)) : p423 ∨ (¬ p536) ∨ (¬ p1465) ∨ (¬ p310) ∨ (¬ p344) ∨ p15 ∨ (¬ p496) ∨ (¬ p726) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19770 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u2)

theorem step32849 (p14 p15 p63 p69 p110 p229 p310 p421 p577 p1055 p1061 p1076 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26833 : p69 ∨ p15)
    (h26849 : p229 ∨ p14)
    (h17600 : (¬ p63) ∨ (¬ p69) ∨ (¬ p110) ∨ (¬ p229) ∨ (¬ p310) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p1061) ∨ (¬ p1076)) : (¬ p110) ∨ p1055 ∨ (¬ p310) ∨ (¬ p421) ∨ (¬ p1076) ∨ (¬ p577) ∨ p15 ∨ (¬ p63) ∨ p14 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h17600 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u4)

theorem step32850 (p63 p161 p310 p344 p421 p577 p1055 p1061 p1076 p1229 p1232 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h26909 : p1061 ∨ p1055)
    (h17605 : (¬ p63) ∨ (¬ p161) ∨ (¬ p310) ∨ (¬ p344) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p1061) ∨ (¬ p1076) ∨ (¬ p1232)) : p1229 ∨ p1055 ∨ (¬ p63) ∨ (¬ p1076) ∨ (¬ p310) ∨ (¬ p421) ∨ (¬ p161) ∨ (¬ p344) ∨ (¬ p577) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1229) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17605 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u3)
  · exact False.elim (q8 u9)

theorem step32851 (p14 p234 p534 p726 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h18853 : (¬ p14) ∨ (¬ p534) ∨ (¬ p726) ∨ (¬ p1187)) : (¬ p534) ∨ p234 ∨ (¬ p14) ∨ (¬ p726) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p234) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18853 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step32853 (p6 p24 p67 p423 p633 p636 p726 p985 p1035 : Prop)
    (h26885 : p636 ∨ p633)
    (h18696 : (¬ p6) ∨ (¬ p24) ∨ (¬ p67) ∨ (¬ p423) ∨ (¬ p636) ∨ (¬ p726) ∨ (¬ p985) ∨ (¬ p1035)) : (¬ p726) ∨ (¬ p24) ∨ (¬ p423) ∨ (¬ p985) ∨ (¬ p6) ∨ (¬ p67) ∨ (¬ p1035) ∨ p633 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p633) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18696 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u6)

theorem step32854 (p158 p536 p726 p918 p928 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26901 : p928 ∨ p918)
    (h17405 : (¬ p158) ∨ (¬ p536) ∨ (¬ p726) ∨ (¬ p928) ∨ (¬ p1077)) : (¬ p536) ∨ (¬ p726) ∨ p1076 ∨ p918 ∨ (¬ p158) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17405 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step32855 (p15 p18 p69 p101 p726 : Prop)
    (h26833 : p69 ∨ p15)
    (h17250 : (¬ p18) ∨ (¬ p69) ∨ (¬ p101) ∨ (¬ p726)) : (¬ p101) ∨ (¬ p726) ∨ p15 ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17250 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)

theorem step32856 (p86 p185 p237 p495 p633 p636 p726 p727 p836 p840 : Prop)
    (h26885 : p636 ∨ p633)
    (h26895 : p840 ∨ p836)
    (h26851 : p237 ∨ p185)
    (h17309 : (¬ p86) ∨ (¬ p237) ∨ (¬ p495) ∨ (¬ p636) ∨ (¬ p726) ∨ (¬ p727) ∨ (¬ p840)) : (¬ p727) ∨ p633 ∨ (¬ p86) ∨ p836 ∨ (¬ p495) ∨ (¬ p726) ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p727 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p633) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17309 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u8)

theorem step32857 (p6 p24 p64 p86 p633 p636 p726 p985 p1346 p1508 : Prop)
    (h26885 : p636 ∨ p633)
    (h18697 : (¬ p6) ∨ (¬ p24) ∨ (¬ p64) ∨ (¬ p86) ∨ (¬ p636) ∨ (¬ p726) ∨ (¬ p985) ∨ (¬ p1346) ∨ (¬ p1508)) : (¬ p726) ∨ p633 ∨ (¬ p1508) ∨ (¬ p86) ∨ (¬ p1346) ∨ (¬ p6) ∨ (¬ p64) ∨ (¬ p24) ∨ (¬ p985) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p633) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18697 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u2)

theorem step32858 (p163 p167 p560 p769 p1074 p1562 : Prop)
    (h26843 : p167 ∨ p163)
    (h20375 : (¬ p167) ∨ (¬ p560) ∨ (¬ p769) ∨ (¬ p1074) ∨ (¬ p1562)) : (¬ p1562) ∨ (¬ p769) ∨ (¬ p560) ∨ p163 ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20375 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)

theorem step32862 (p86 p495 p789 p790 p1325 p1333 p1454 p1604 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h20261 : (¬ p86) ∨ (¬ p495) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1333) ∨ (¬ p1454) ∨ (¬ p1604)) : (¬ p1604) ∨ (¬ p789) ∨ (¬ p86) ∨ (¬ p790) ∨ (¬ p495) ∨ (¬ p1454) ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1604 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1454 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20261 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u0)

theorem step32863 (p12 p39 p63 p68 p106 p495 p561 p633 p636 p1036 p1055 p1061 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26907 : p1036 ∨ p12)
    (h26885 : p636 ∨ p633)
    (h19287 : (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p106) ∨ (¬ p495) ∨ (¬ p561) ∨ (¬ p636) ∨ (¬ p1036) ∨ (¬ p1061)) : (¬ p68) ∨ (¬ p561) ∨ (¬ p106) ∨ p1055 ∨ (¬ p495) ∨ (¬ p39) ∨ p12 ∨ (¬ p63) ∨ p633 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p633) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h19287 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u9)

theorem step32865 (p63 p344 p346 p495 p633 p636 : Prop)
    (h26885 : p636 ∨ p633)
    (h26863 : p346 ∨ p344)
    (h17680 : (¬ p63) ∨ (¬ p346) ∨ (¬ p495) ∨ (¬ p636)) : p633 ∨ p344 ∨ (¬ p495) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17680 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step32866 (p63 p101 p102 p495 p633 p636 : Prop)
    (h26885 : p636 ∨ p633)
    (h26837 : p102 ∨ p101)
    (h18501 : (¬ p63) ∨ (¬ p102) ∨ (¬ p495) ∨ (¬ p636)) : p633 ∨ (¬ p495) ∨ (¬ p63) ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18501 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step32867 (p86 p185 p237 p286 p495 p633 p636 : Prop)
    (h26885 : p636 ∨ p633)
    (h26851 : p237 ∨ p185)
    (h17029 : (¬ p86) ∨ (¬ p237) ∨ (¬ p286) ∨ (¬ p495) ∨ (¬ p636)) : p633 ∨ (¬ p286) ∨ (¬ p495) ∨ (¬ p86) ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17029 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step32868 (p86 p455 p456 p495 p532 p790 p1022 p1330 : Prop)
    (h26871 : p456 ∨ p455)
    (h17345 : (¬ p86) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p532) ∨ (¬ p790) ∨ (¬ p1022) ∨ (¬ p1330)) : (¬ p1022) ∨ p455 ∨ (¬ p532) ∨ (¬ p1330) ∨ (¬ p86) ∨ (¬ p495) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p455) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17345 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u3)

theorem step32869 (p41 p45 p435 p687 p816 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h26831 : p45 ∨ p41)
    (h17568 : (¬ p45) ∨ (¬ p435) ∨ (¬ p687) ∨ (¬ p816) ∨ (¬ p1393)) : (¬ p687) ∨ p1385 ∨ (¬ p816) ∨ (¬ p435) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17568 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step32870 (p15 p69 p86 p234 p435 p1187 p1335 p1346 p1508 : Prop)
    (h26833 : p69 ∨ p15)
    (h26921 : p1187 ∨ p234)
    (h18722 : (¬ p69) ∨ (¬ p86) ∨ (¬ p435) ∨ (¬ p1187) ∨ (¬ p1335) ∨ (¬ p1346) ∨ (¬ p1508)) : (¬ p1346) ∨ (¬ p1508) ∨ (¬ p435) ∨ p15 ∨ (¬ p1335) ∨ p234 ∨ (¬ p86) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18722 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u1)

theorem step32871 (p435 p595 p616 p1195 p1548 p1674 : Prop)
    (h26883 : p616 ∨ p595)
    (h17753 : (¬ p435) ∨ (¬ p616) ∨ (¬ p1195) ∨ (¬ p1548) ∨ (¬ p1674)) : (¬ p1674) ∨ (¬ p1548) ∨ (¬ p435) ∨ p595 ∨ (¬ p1195) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1674 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1548 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17753 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step32872 (p41 p419 p435 p795 p996 p1022 : Prop)
    (h26905 : p996 ∨ p419)
    (h19661 : (¬ p41) ∨ (¬ p435) ∨ (¬ p795) ∨ (¬ p996) ∨ (¬ p1022)) : (¬ p1022) ∨ p419 ∨ (¬ p435) ∨ (¬ p795) ∨ (¬ p41) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p795 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19661 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step32873 (p435 p539 p728 p886 p897 p904 : Prop)
    (h26899 : p904 ∨ p897)
    (h17112 : (¬ p435) ∨ (¬ p539) ∨ (¬ p728) ∨ (¬ p886) ∨ (¬ p904)) : p897 ∨ (¬ p728) ∨ (¬ p435) ∨ (¬ p886) ∨ (¬ p539) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p897) := fun hu => hn (Or.inl hu)
  have u1 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p886 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p539 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17112 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step32875 (p172 p435 p539 p728 p836 p840 : Prop)
    (h26895 : p840 ∨ p836)
    (h19070 : (¬ p172) ∨ (¬ p435) ∨ (¬ p539) ∨ (¬ p728) ∨ (¬ p840)) : (¬ p728) ∨ (¬ p539) ∨ (¬ p435) ∨ (¬ p172) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p539 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19070 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step32876 (p2 p6 p127 p435 p1542 : Prop)
    (h26839 : p127 ∨ p6)
    (h20207 : (¬ p2) ∨ (¬ p127) ∨ (¬ p435) ∨ (¬ p1542)) : (¬ p1542) ∨ (¬ p2) ∨ (¬ p435) ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20207 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)

theorem step32877 (p17 p84 p135 p256 p419 p435 p795 p836 p918 p996 p1022 : Prop)
    (h26905 : p996 ∨ p419)
    (h26853 : p256 ∨ p17)
    (h20173 : (¬ p84) ∨ (¬ p135) ∨ (¬ p256) ∨ (¬ p435) ∨ (¬ p795) ∨ (¬ p836) ∨ (¬ p918) ∨ (¬ p996) ∨ (¬ p1022)) : p419 ∨ p17 ∨ (¬ p1022) ∨ (¬ p918) ∨ (¬ p836) ∨ (¬ p84) ∨ (¬ p135) ∨ (¬ p435) ∨ (¬ p795) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p795 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20173 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u2)

theorem step32878 (p324 p420 p434 p435 p601 : Prop)
    (h26881 : p601 ∨ p420)
    (h26209 : (¬ p324) ∨ (¬ p435) ∨ (¬ p601) ∨ (¬ p434)) : (¬ p434) ∨ (¬ p324) ∨ p420 ∨ (¬ p435) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p324 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h26209 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step32879 (p63 p126 p347 p424 p435 p576 p581 p728 p796 : Prop)
    (h26879 : p581 ∨ p576)
    (h26891 : p796 ∨ p424)
    (h18581 : (¬ p63) ∨ (¬ p126) ∨ (¬ p347) ∨ (¬ p435) ∨ (¬ p581) ∨ (¬ p728) ∨ (¬ p796)) : (¬ p728) ∨ (¬ p347) ∨ p576 ∨ (¬ p435) ∨ (¬ p126) ∨ p424 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p424) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18581 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u8)

theorem step32880 (p47 p87 p158 p189 p234 p435 p536 p735 p918 p928 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26901 : p928 ∨ p918)
    (h19824 : (¬ p47) ∨ (¬ p87) ∨ (¬ p158) ∨ (¬ p189) ∨ (¬ p435) ∨ (¬ p536) ∨ (¬ p735) ∨ (¬ p928) ∨ (¬ p1187)) : p234 ∨ (¬ p735) ∨ (¬ p158) ∨ (¬ p536) ∨ (¬ p189) ∨ (¬ p87) ∨ (¬ p435) ∨ (¬ p47) ∨ p918 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p735 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h19824 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u9)

theorem step32881 (p17 p101 p102 p140 p189 p256 p435 p455 p456 p600 p1080 p1542 : Prop)
    (h26871 : p456 ∨ p455)
    (h26853 : p256 ∨ p17)
    (h26837 : p102 ∨ p101)
    (h18647 : (¬ p102) ∨ (¬ p140) ∨ (¬ p189) ∨ (¬ p256) ∨ (¬ p435) ∨ (¬ p456) ∨ (¬ p600) ∨ (¬ p1080) ∨ (¬ p1542)) : (¬ p1542) ∨ p455 ∨ (¬ p189) ∨ (¬ p1080) ∨ p17 ∨ (¬ p435) ∨ (¬ p140) ∨ (¬ p600) ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p455) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p600 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h18647 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u11)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u3)
  · exact False.elim (q8 u0)

theorem step32882 (p8 p106 p135 p189 p265 p305 p344 p435 p539 p687 p710 p820 : Prop)
    (h26889 : p710 ∨ p8)
    (h20048 : (¬ p106) ∨ (¬ p135) ∨ (¬ p189) ∨ (¬ p265) ∨ (¬ p305) ∨ (¬ p344) ∨ (¬ p435) ∨ (¬ p539) ∨ (¬ p687) ∨ (¬ p710) ∨ (¬ p820)) : (¬ p687) ∨ (¬ p305) ∨ (¬ p189) ∨ (¬ p344) ∨ (¬ p135) ∨ p8 ∨ (¬ p265) ∨ (¬ p539) ∨ (¬ p435) ∨ (¬ p106) ∨ (¬ p820) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p539 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p820 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20048 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u0)
  · exact False.elim (q9 u11)
  · exact False.elim (q10 u10)

theorem step32885 (p225 p542 p544 p546 p547 p548 p549 p550 : Prop)
    (h26876 : (¬ p225) ∨ (¬ p544))
    (h3009 : p542 ∨ p544 ∨ (¬ p546) ∨ (¬ p547) ∨ (¬ p548) ∨ (¬ p549) ∨ (¬ p550)) : (¬ p549) ∨ (¬ p548) ∨ (¬ p546) ∨ (¬ p225) ∨ p542 ∨ (¬ p550) ∨ (¬ p547) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p549 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p548 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p546 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p542) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p550 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p547 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p544) := by
    rcases h26876 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h3009 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u5)

theorem step32886 (p12 p883 p1036 p1074 : Prop)
    (h26906 : (¬ p12) ∨ (¬ p1036))
    (h13161 : (¬ p883) ∨ p1036 ∨ (¬ p1074)) : (¬ p883) ∨ (¬ p1074) ∨ (¬ p12) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1036) := by
    rcases h26906 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h13161 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u1)

theorem step32887 (p15 p18 p69 p109 p883 p1096 : Prop)
    (h26833 : p69 ∨ p15)
    (h16687 : (¬ p18) ∨ (¬ p69) ∨ (¬ p109) ∨ (¬ p883) ∨ (¬ p1096)) : p15 ∨ (¬ p18) ∨ (¬ p109) ∨ (¬ p883) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p15) := fun hu => hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16687 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)

theorem step32888 (p125 p362 p366 p367 : Prop)
    (h26864 : (¬ p125) ∨ (¬ p362))
    (h20919 : p366 ∨ p367 ∨ p362) : p366 ∨ p367 ∨ (¬ p125) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p366) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p367) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p362) := by
    rcases h26864 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h20919 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (u3 q2)

theorem step32895 (p382 p406 p420 p421 p455 p456 : Prop)
    (h26870 : (¬ p455) ∨ (¬ p456))
    (h26868 : (¬ p382) ∨ (¬ p406))
    (h20950 : (¬ p420) ∨ p456 ∨ (¬ p421) ∨ (¬ p382) ∨ p406) : (¬ p420) ∨ (¬ p421) ∨ (¬ p455) ∨ (¬ p382) := by
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
  have u2 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p456) := by
    rcases h26870 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u5 : (¬ p406) := by
    rcases h26868 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h20950 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (u5 q4)

theorem step32896 (p125 p362 p382 p406 p420 p455 p456 : Prop)
    (h26870 : (¬ p455) ∨ (¬ p456))
    (h26868 : (¬ p382) ∨ (¬ p406))
    (h26864 : (¬ p125) ∨ (¬ p362))
    (h20930 : p456 ∨ p362 ∨ (¬ p420) ∨ (¬ p382) ∨ p406) : (¬ p420) ∨ (¬ p455) ∨ (¬ p382) ∨ (¬ p125) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p456) := by
    rcases h26870 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u5 : (¬ p406) := by
    rcases h26868 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u6 : (¬ p362) := by
    rcases h26864 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h20930 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u4 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)

theorem step32898 (p17 p135 p256 p382 p789 p795 p815 : Prop)
    (h26853 : p256 ∨ p17)
    (h19212 : (¬ p135) ∨ (¬ p256) ∨ (¬ p382) ∨ (¬ p789) ∨ (¬ p795) ∨ (¬ p815)) : (¬ p382) ∨ (¬ p789) ∨ p17 ∨ (¬ p815) ∨ (¬ p135) ∨ (¬ p795) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p815 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p795 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19212 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)

theorem step32900 (p63 p126 p331 p382 p419 p576 p581 p621 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26879 : p581 ∨ p576)
    (h18518 : (¬ p63) ∨ (¬ p126) ∨ (¬ p331) ∨ (¬ p382) ∨ (¬ p581) ∨ (¬ p621) ∨ (¬ p996)) : p419 ∨ (¬ p382) ∨ (¬ p126) ∨ (¬ p63) ∨ (¬ p621) ∨ p576 ∨ (¬ p331) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p621 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18518 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u7)

theorem step32902 (p663 p728 p897 p904 p1074 : Prop)
    (h26899 : p904 ∨ p897)
    (h26211 : (¬ p1074) ∨ (¬ p904) ∨ (¬ p663) ∨ (¬ p728)) : (¬ p728) ∨ (¬ p663) ∨ (¬ p1074) ∨ p897 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p663 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h26211 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)

theorem step32903 (p63 p980 p1074 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h18181 : (¬ p63) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1099)) : p1096 ∨ (¬ p1074) ∨ (¬ p980) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1096) := fun hu => hn (Or.inl hu)
  have u1 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18181 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step32904 (p17 p86 p256 p980 p1074 p1096 p1099 p1449 p1651 : Prop)
    (h26853 : p256 ∨ p17)
    (h26913 : p1099 ∨ p1096)
    (h18866 : (¬ p86) ∨ (¬ p256) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1449) ∨ (¬ p1651)) : (¬ p1651) ∨ p17 ∨ (¬ p1449) ∨ (¬ p980) ∨ (¬ p1074) ∨ p1096 ∨ (¬ p86) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1651 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18866 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u0)

theorem step32905 (p86 p790 p980 p1022 p1074 p1096 p1099 p1330 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h17031 : (¬ p86) ∨ (¬ p790) ∨ (¬ p980) ∨ (¬ p1022) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1330)) : (¬ p1022) ∨ (¬ p790) ∨ (¬ p1074) ∨ (¬ p980) ∨ p1096 ∨ (¬ p86) ∨ (¬ p1330) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17031 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u6)

theorem step32906 (p9 p63 p85 p929 p1055 p1061 p1074 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26835 : p85 ∨ p63)
    (h16530 : (¬ p9) ∨ (¬ p85) ∨ (¬ p929) ∨ (¬ p1061) ∨ (¬ p1074)) : p1055 ∨ (¬ p1074) ∨ (¬ p9) ∨ (¬ p929) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1055) := fun hu => hn (Or.inl hu)
  have u1 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16530 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)

theorem step32907 (p9 p495 p641 p1055 p1061 p1074 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h17638 : (¬ p9) ∨ (¬ p495) ∨ (¬ p641) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p641) ∨ p1055 ∨ (¬ p9) ∨ (¬ p495) ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p641 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17638 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)

theorem step32908 (p9 p15 p39 p69 p922 p1055 p1061 p1074 : Prop)
    (h26833 : p69 ∨ p15)
    (h26909 : p1061 ∨ p1055)
    (h20441 : (¬ p9) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p922) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p9) ∨ p15 ∨ (¬ p922) ∨ (¬ p1074) ∨ p1055 ∨ (¬ p39) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p922 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20441 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u3)

theorem step32909 (p6 p127 p980 p1074 p1096 p1099 p1449 p1665 : Prop)
    (h26839 : p127 ∨ p6)
    (h26913 : p1099 ∨ p1096)
    (h26212 : (¬ p1665) ∨ (¬ p1099) ∨ (¬ p127) ∨ (¬ p1449) ∨ (¬ p980) ∨ (¬ p1074)) : (¬ p1665) ∨ (¬ p1074) ∨ (¬ p1449) ∨ (¬ p980) ∨ p6 ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1074 := by
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
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u7 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h26212 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u1)

theorem step32910 (p9 p16 p101 p134 p189 p897 p904 p1055 p1061 p1074 : Prop)
    (h26899 : p904 ∨ p897)
    (h26909 : p1061 ∨ p1055)
    (h20008 : (¬ p9) ∨ (¬ p16) ∨ (¬ p101) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p904) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p101) ∨ (¬ p1074) ∨ (¬ p9) ∨ p897 ∨ p1055 ∨ (¬ p134) ∨ (¬ p16) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20008 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u1)

theorem step32911 (p135 p158 p170 p576 p581 p922 p1055 p1061 p1074 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26879 : p581 ∨ p576)
    (h19223 : (¬ p135) ∨ (¬ p158) ∨ (¬ p170) ∨ (¬ p581) ∨ (¬ p922) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p922) ∨ p1055 ∨ (¬ p170) ∨ (¬ p1074) ∨ p576 ∨ (¬ p135) ∨ (¬ p158) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p922 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19223 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step32913 (p455 p456 p464 p470 p471 p472 p473 p474 : Prop)
    (h26870 : (¬ p455) ∨ (¬ p456))
    (h2514 : p456 ∨ p464 ∨ (¬ p470) ∨ (¬ p471) ∨ (¬ p472) ∨ (¬ p473) ∨ (¬ p474)) : (¬ p474) ∨ p464 ∨ (¬ p455) ∨ (¬ p471) ∨ (¬ p470) ∨ (¬ p473) ∨ (¬ p472) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p474 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p464) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p471 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p470 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p473 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p472 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p456) := by
    rcases h26870 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h2514 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u0)

theorem step32941 (p17 p84 p121 p140 p255 p256 p918 p1084 : Prop)
    (h26853 : p256 ∨ p17)
    (h20174 : (¬ p84) ∨ (¬ p121) ∨ (¬ p140) ∨ (¬ p255) ∨ (¬ p256) ∨ (¬ p918) ∨ (¬ p1084)) : (¬ p255) ∨ p17 ∨ (¬ p121) ∨ (¬ p918) ∨ (¬ p1084) ∨ (¬ p84) ∨ (¬ p140) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20174 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)

theorem step32947 (p8 p351 p710 : Prop)
    (h26889 : p710 ∨ p8)
    (h16775 : p351 ∨ (¬ p710)) : p351 ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p351) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p8) := fun hu => hn (Or.inr hu)
  have u2 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16775 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)

theorem step32948 (p8 p710 p980 p983 p1055 p1061 p1325 : Prop)
    (h26903 : p983 ∨ p980)
    (h26909 : p1061 ∨ p1055)
    (h26889 : p710 ∨ p8)
    (h17035 : (¬ p710) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1325)) : p980 ∨ p1055 ∨ p8 ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17035 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)

theorem step32949 (p8 p710 p836 p840 p980 p1115 : Prop)
    (h26889 : p710 ∨ p8)
    (h26895 : p840 ∨ p836)
    (h19976 : (¬ p710) ∨ (¬ p840) ∨ (¬ p980) ∨ (¬ p1115)) : (¬ p1115) ∨ p8 ∨ (¬ p980) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p8) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19976 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)

theorem step32950 (p8 p41 p63 p163 p224 p710 p1103 p1325 : Prop)
    (h26889 : p710 ∨ p8)
    (h18568 : (¬ p41) ∨ (¬ p63) ∨ (¬ p163) ∨ (¬ p224) ∨ (¬ p710) ∨ (¬ p1103) ∨ (¬ p1325)) : (¬ p41) ∨ (¬ p1103) ∨ (¬ p163) ∨ p8 ∨ (¬ p1325) ∨ (¬ p63) ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18568 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u4)

theorem step32952 (p8 p13 p18 p210 p344 p710 p959 p1095 p1102 p1226 p1452 : Prop)
    (h26889 : p710 ∨ p8)
    (h20588 : (¬ p13) ∨ (¬ p18) ∨ (¬ p210) ∨ (¬ p344) ∨ (¬ p710) ∨ (¬ p959) ∨ (¬ p1095) ∨ (¬ p1102) ∨ (¬ p1226) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p959) ∨ (¬ p1102) ∨ (¬ p1095) ∨ (¬ p13) ∨ (¬ p210) ∨ (¬ p18) ∨ (¬ p1226) ∨ p8 ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p959 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h20588 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u0)

theorem step32954 (p8 p225 p544 p560 p710 : Prop)
    (h26877 : p544 ∨ p225)
    (h26889 : p710 ∨ p8)
    (h4149 : (¬ p544) ∨ (¬ p560) ∨ (¬ p710)) : p225 ∨ (¬ p560) ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h4149 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)

theorem step32955 (p8 p41 p45 p135 p265 p305 p710 p897 p904 p927 : Prop)
    (h26889 : p710 ∨ p8)
    (h26831 : p45 ∨ p41)
    (h26899 : p904 ∨ p897)
    (h20052 : (¬ p45) ∨ (¬ p135) ∨ (¬ p265) ∨ (¬ p305) ∨ (¬ p710) ∨ (¬ p904) ∨ (¬ p927)) : (¬ p305) ∨ (¬ p265) ∨ p8 ∨ (¬ p927) ∨ p41 ∨ (¬ p135) ∨ p897 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20052 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u3)

theorem step32956 (p8 p662 p710 p1055 : Prop)
    (h26889 : p710 ∨ p8)
    (h10740 : (¬ p662) ∨ (¬ p710) ∨ p1055) : p1055 ∨ p8 ∨ (¬ p662) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1055) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p8) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p662 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h10740 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (u0 q2)

theorem step32962 (p63 p85 p303 p351 p363 p382 p387 p425 p582 p662 p1095 p1096 : Prop)
    (h26867 : p387 ∨ p303)
    (h26835 : p85 ∨ p63)
    (h16557 : (¬ p85) ∨ (¬ p351) ∨ (¬ p363) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p662) ∨ (¬ p1095) ∨ (¬ p1096)) : (¬ p1096) ∨ (¬ p363) ∨ (¬ p425) ∨ p303 ∨ (¬ p582) ∨ (¬ p1095) ∨ p63 ∨ (¬ p351) ∨ (¬ p382) ∨ (¬ p662) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p363 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p662 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h16557 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u11)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u0)

theorem step32964 (p11 p17 p86 p256 p595 p616 p1335 p1443 p1452 p1545 : Prop)
    (h26883 : p616 ∨ p595)
    (h26935 : p1443 ∨ p11)
    (h26853 : p256 ∨ p17)
    (h17547 : (¬ p86) ∨ (¬ p256) ∨ (¬ p616) ∨ (¬ p1335) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p1545)) : (¬ p1452) ∨ (¬ p1545) ∨ (¬ p86) ∨ p595 ∨ (¬ p1335) ∨ p11 ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u9 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17547 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u1)

theorem step32965 (p134 p595 p616 p795 p1022 p1545 : Prop)
    (h26883 : p616 ∨ p595)
    (h16842 : (¬ p134) ∨ (¬ p616) ∨ (¬ p795) ∨ (¬ p1022) ∨ (¬ p1545)) : (¬ p1022) ∨ (¬ p134) ∨ p595 ∨ (¬ p795) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p795 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16842 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)

theorem step32966 (p84 p495 p499 p582 p595 p616 p1335 p1346 p1508 p1545 : Prop)
    (h26875 : p499 ∨ p495)
    (h26883 : p616 ∨ p595)
    (h18764 : (¬ p84) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p616) ∨ (¬ p1335) ∨ (¬ p1346) ∨ (¬ p1508) ∨ (¬ p1545)) : p495 ∨ (¬ p1346) ∨ p595 ∨ (¬ p84) ∨ (¬ p582) ∨ (¬ p1508) ∨ (¬ p1335) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18764 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u7)

theorem step32967 (p2 p6 p127 p434 p1192 p1545 : Prop)
    (h26839 : p127 ∨ p6)
    (h20208 : (¬ p2) ∨ (¬ p127) ∨ (¬ p434) ∨ (¬ p1192) ∨ (¬ p1545)) : (¬ p2) ∨ (¬ p434) ∨ (¬ p1192) ∨ (¬ p1545) ∨ p6 := by
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
  have u2 : p1192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20208 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)

theorem step32968 (p86 p185 p237 p595 p616 p980 p983 p1115 p1116 p1335 p1545 : Prop)
    (h26903 : p983 ∨ p980)
    (h26915 : p1116 ∨ p1115)
    (h26851 : p237 ∨ p185)
    (h26883 : p616 ∨ p595)
    (h17545 : (¬ p86) ∨ (¬ p237) ∨ (¬ p616) ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1335) ∨ (¬ p1545)) : p980 ∨ p1115 ∨ (¬ p1335) ∨ p185 ∨ (¬ p1545) ∨ p595 ∨ (¬ p86) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1115) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17545 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u4)

theorem step32989 (p41 p63 p595 p616 p799 p1388 : Prop)
    (h26883 : p616 ∨ p595)
    (h19684 : (¬ p41) ∨ (¬ p63) ∨ (¬ p616) ∨ (¬ p799) ∨ (¬ p1388)) : p595 ∨ (¬ p41) ∨ (¬ p63) ∨ (¬ p1388) ∨ (¬ p799) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p595) := fun hu => hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1388 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p799 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19684 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)

theorem step32990 (p63 p595 p616 p924 p980 p983 p1015 p1055 p1061 p1098 p1335 p1388 : Prop)
    (h26883 : p616 ∨ p595)
    (h26909 : p1061 ∨ p1055)
    (h26903 : p983 ∨ p980)
    (h20020 : (¬ p63) ∨ (¬ p616) ∨ (¬ p924) ∨ (¬ p983) ∨ (¬ p1015) ∨ (¬ p1061) ∨ (¬ p1098) ∨ (¬ p1335) ∨ (¬ p1388)) : (¬ p1015) ∨ p595 ∨ (¬ p1388) ∨ (¬ p924) ∨ (¬ p1335) ∨ p1055 ∨ (¬ p1098) ∨ (¬ p63) ∨ p980 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1388 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1098 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h20020 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u2)

theorem step32992 (p17 p84 p256 p258 p288 p382 p533 p619 p756 p1325 p1394 : Prop)
    (h26853 : p256 ∨ p17)
    (h26855 : p288 ∨ p258)
    (h16949 : (¬ p84) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p382) ∨ (¬ p533) ∨ (¬ p619) ∨ (¬ p756) ∨ (¬ p1325) ∨ (¬ p1394)) : (¬ p756) ∨ p17 ∨ (¬ p382) ∨ (¬ p619) ∨ (¬ p1394) ∨ (¬ p84) ∨ p258 ∨ (¬ p1325) ∨ (¬ p533) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p619 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1394 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h16949 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u4)

theorem step32995 (p595 p616 p622 p628 p629 p630 p631 p632 : Prop)
    (h26882 : (¬ p595) ∨ (¬ p616))
    (h3529 : p616 ∨ p622 ∨ (¬ p628) ∨ (¬ p629) ∨ (¬ p630) ∨ (¬ p631) ∨ (¬ p632)) : (¬ p632) ∨ p622 ∨ (¬ p595) ∨ (¬ p629) ∨ (¬ p628) ∨ (¬ p631) ∨ (¬ p630) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p632 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p622) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p629 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p628 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p631 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p630 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p616) := by
    rcases h26882 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h3529 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u0)

theorem step32999 (p533 p980 p983 : Prop)
    (h26903 : p983 ∨ p980)
    (h17898 : p533 ∨ (¬ p983)) : p533 ∨ p980 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p533) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr hu)
  have u2 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17898 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)

theorem step33000 (p663 p980 p983 p1325 p1333 : Prop)
    (h26903 : p983 ∨ p980)
    (h26930 : (¬ p1325) ∨ (¬ p1333))
    (h14141 : (¬ p663) ∨ (¬ p983) ∨ p1333) : p980 ∨ (¬ p663) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : p663 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : (¬ p1333) := by
    rcases h26930 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h14141 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (u4 q2)

theorem step33001 (p6 p14 p72 p121 p127 p229 p980 p983 p1037 p1081 p1465 : Prop)
    (h26849 : p229 ∨ p14)
    (h26903 : p983 ∨ p980)
    (h26839 : p127 ∨ p6)
    (h19674 : (¬ p72) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p229) ∨ (¬ p983) ∨ (¬ p1037) ∨ (¬ p1081) ∨ (¬ p1465)) : (¬ p1037) ∨ (¬ p1465) ∨ p14 ∨ p980 ∨ (¬ p121) ∨ (¬ p72) ∨ p6 ∨ (¬ p1081) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1037 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19674 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u1)

theorem step33004 (p15 p161 p980 p983 p1229 p1232 : Prop)
    (h26903 : p983 ∨ p980)
    (h26927 : p1232 ∨ p1229)
    (h18905 : (¬ p15) ∨ (¬ p161) ∨ (¬ p983) ∨ (¬ p1232)) : p980 ∨ p1229 ∨ (¬ p161) ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18905 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step33007 (p63 p85 p425 p532 p582 p961 p980 p983 p1229 p1309 : Prop)
    (h26835 : p85 ∨ p63)
    (h26903 : p983 ∨ p980)
    (h16745 : (¬ p85) ∨ (¬ p425) ∨ (¬ p532) ∨ (¬ p582) ∨ (¬ p961) ∨ (¬ p983) ∨ (¬ p1229) ∨ (¬ p1309)) : (¬ p425) ∨ (¬ p961) ∨ (¬ p582) ∨ p63 ∨ (¬ p1229) ∨ p980 ∨ (¬ p532) ∨ (¬ p1309) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h16745 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step33008 (p86 p125 p185 p237 p420 p494 p601 p633 p636 p980 p983 p1115 p1116 : Prop)
    (h26903 : p983 ∨ p980)
    (h26851 : p237 ∨ p185)
    (h26885 : p636 ∨ p633)
    (h26881 : p601 ∨ p420)
    (h26915 : p1116 ∨ p1115)
    (h17320 : (¬ p86) ∨ (¬ p125) ∨ (¬ p237) ∨ (¬ p494) ∨ (¬ p601) ∨ (¬ p636) ∨ (¬ p983) ∨ (¬ p1116)) : p980 ∨ p185 ∨ (¬ p125) ∨ p633 ∨ p420 ∨ p1115 ∨ (¬ p86) ∨ (¬ p494) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p633) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u12 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17320 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u12)

theorem step33009 (p3 p14 p192 p226 p422 p980 p983 p1041 p1256 : Prop)
    (h26847 : p226 ∨ p3)
    (h26903 : p983 ∨ p980)
    (h26929 : p1256 ∨ p422)
    (h17312 : (¬ p14) ∨ (¬ p192) ∨ (¬ p226) ∨ (¬ p983) ∨ (¬ p1041) ∨ (¬ p1256)) : p3 ∨ p980 ∨ (¬ p14) ∨ (¬ p192) ∨ p422 ∨ (¬ p1041) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1041 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17312 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u8)

theorem step33011 (p63 p918 p928 p980 p983 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h26903 : p983 ∨ p980)
    (h26901 : p928 ∨ p918)
    (h18598 : (¬ p63) ∨ (¬ p928) ∨ (¬ p983) ∨ (¬ p1116)) : p1115 ∨ p980 ∨ p918 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1115) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18598 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step33014 (p158 p1055 p1061 p1115 p1116 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26914 : (¬ p1115) ∨ (¬ p1116))
    (h14967 : (¬ p158) ∨ (¬ p1061) ∨ p1116) : p1055 ∨ (¬ p1115) ∨ (¬ p158) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1055) := fun hu => hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : (¬ p1116) := by
    rcases h26914 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h14967 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (u4 q2)

theorem step33015 (p14 p165 p422 p536 p557 p1256 p1584 : Prop)
    (h26929 : p1256 ∨ p422)
    (h17311 : (¬ p14) ∨ (¬ p165) ∨ (¬ p536) ∨ (¬ p557) ∨ (¬ p1256) ∨ (¬ p1584)) : (¬ p165) ∨ (¬ p536) ∨ (¬ p14) ∨ (¬ p1584) ∨ p422 ∨ (¬ p557) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p165 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17311 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)

theorem step33017 (p12 p108 p121 p1036 p1079 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26906 : (¬ p12) ∨ (¬ p1036))
    (h8773 : (¬ p108) ∨ p1036 ∨ (¬ p1079) ∨ (¬ p1206)) : p121 ∨ (¬ p12) ∨ (¬ p1079) ∨ (¬ p108) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1079 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : (¬ p1036) := by
    rcases h26906 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h8773 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step33024 (p15 p44 p63 p69 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h26833 : p69 ∨ p15)
    (h26244 : (¬ p63) ∨ (¬ p1393) ∨ (¬ p44) ∨ (¬ p69)) : p1385 ∨ p15 ∨ (¬ p63) ∨ (¬ p44) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1385) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h26244 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)

theorem step33025 (p3 p14 p48 p64 p226 p495 p499 p582 : Prop)
    (h26847 : p226 ∨ p3)
    (h26875 : p499 ∨ p495)
    (h16810 : (¬ p14) ∨ (¬ p48) ∨ (¬ p64) ∨ (¬ p226) ∨ (¬ p499) ∨ (¬ p582)) : p3 ∨ (¬ p14) ∨ (¬ p582) ∨ p495 ∨ (¬ p48) ∨ (¬ p64) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16810 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)

theorem step33027 (p3 p14 p39 p63 p64 p226 : Prop)
    (h26847 : p226 ∨ p3)
    (h17618 : (¬ p14) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p64) ∨ (¬ p226)) : p3 ∨ (¬ p14) ∨ (¬ p64) ∨ (¬ p39) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17618 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step33028 (p14 p20 p109 p125 p207 p362 p420 : Prop)
    (h26865 : p362 ∨ p125)
    (h19371 : (¬ p14) ∨ (¬ p20) ∨ (¬ p109) ∨ (¬ p207) ∨ (¬ p362) ∨ (¬ p420)) : (¬ p420) ∨ (¬ p20) ∨ (¬ p109) ∨ p125 ∨ (¬ p207) ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p20 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19371 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u0)

theorem step33029 (p3 p14 p17 p64 p86 p126 p226 p234 p256 p331 p1187 : Prop)
    (h26847 : p226 ∨ p3)
    (h26921 : p1187 ∨ p234)
    (h26853 : p256 ∨ p17)
    (h18860 : (¬ p14) ∨ (¬ p64) ∨ (¬ p86) ∨ (¬ p126) ∨ (¬ p226) ∨ (¬ p256) ∨ (¬ p331) ∨ (¬ p1187)) : p3 ∨ p234 ∨ p17 ∨ (¬ p64) ∨ (¬ p86) ∨ (¬ p14) ∨ (¬ p126) ∨ (¬ p331) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p234) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p126 := by
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
  have u9 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18860 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u9)

theorem step33030 (p14 p50 p165 p557 p1055 p1061 p1115 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h17375 : (¬ p14) ∨ (¬ p50) ∨ (¬ p165) ∨ (¬ p557) ∨ (¬ p1061) ∨ (¬ p1115)) : p1055 ∨ (¬ p557) ∨ (¬ p1115) ∨ (¬ p165) ∨ (¬ p14) ∨ (¬ p50) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1055) := fun hu => hn (Or.inl hu)
  have u1 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p165 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p50 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17375 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)

theorem step33032 (p3 p6 p10 p14 p127 p226 p323 : Prop)
    (h26847 : p226 ∨ p3)
    (h26839 : p127 ∨ p6)
    (h26861 : p323 ∨ p10)
    (h19261 : (¬ p14) ∨ (¬ p127) ∨ (¬ p226) ∨ (¬ p323)) : p3 ∨ p6 ∨ p10 ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
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
    · exact False.elim (u2 q1)
  rcases h19261 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)

theorem step33033 (p12 p225 p544 p663 p728 p1036 : Prop)
    (h26877 : p544 ∨ p225)
    (h26907 : p1036 ∨ p12)
    (h26245 : (¬ p1036) ∨ (¬ p544) ∨ (¬ p663) ∨ (¬ p728)) : p225 ∨ (¬ p728) ∨ (¬ p663) ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p663 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h26245 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)

theorem step33034 (p3 p12 p226 p1036 p1044 : Prop)
    (h26847 : p226 ∨ p3)
    (h26907 : p1036 ∨ p12)
    (h16836 : (¬ p226) ∨ (¬ p1036) ∨ p1044) : p1044 ∨ p3 ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1044) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p12) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u4 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16836 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (u0 q2)

theorem step33035 (p3 p5 p12 p89 p226 p790 p1036 p1120 p1273 p1385 : Prop)
    (h26847 : p226 ∨ p3)
    (h26907 : p1036 ∨ p12)
    (h18089 : (¬ p5) ∨ (¬ p89) ∨ (¬ p226) ∨ (¬ p790) ∨ (¬ p1036) ∨ (¬ p1120) ∨ (¬ p1273) ∨ (¬ p1385)) : (¬ p790) ∨ p3 ∨ (¬ p1120) ∨ (¬ p1273) ∨ (¬ p1385) ∨ (¬ p5) ∨ (¬ p89) ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18089 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step33036 (p12 p157 p158 p160 p172 p980 p1036 : Prop)
    (h26907 : p1036 ∨ p12)
    (h19208 : (¬ p157) ∨ (¬ p158) ∨ (¬ p160) ∨ (¬ p172) ∨ (¬ p980) ∨ (¬ p1036)) : (¬ p160) ∨ (¬ p157) ∨ (¬ p158) ∨ p12 ∨ (¬ p172) ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p157 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19208 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)

theorem step33037 (p3 p5 p12 p63 p226 p285 p918 p928 p1036 p1076 p1077 : Prop)
    (h26847 : p226 ∨ p3)
    (h26911 : p1077 ∨ p1076)
    (h26901 : p928 ∨ p918)
    (h26907 : p1036 ∨ p12)
    (h19690 : (¬ p5) ∨ (¬ p63) ∨ (¬ p226) ∨ (¬ p285) ∨ (¬ p928) ∨ (¬ p1036) ∨ (¬ p1077)) : p3 ∨ p1076 ∨ p918 ∨ (¬ p5) ∨ (¬ p285) ∨ p12 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p285 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19690 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u8)

theorem step33039 (p8 p12 p14 p47 p87 p158 p189 p229 p664 p918 p928 p1036 : Prop)
    (h26849 : p229 ∨ p14)
    (h26907 : p1036 ∨ p12)
    (h26901 : p928 ∨ p918)
    (h19590 : (¬ p8) ∨ (¬ p47) ∨ (¬ p87) ∨ (¬ p158) ∨ (¬ p189) ∨ (¬ p229) ∨ (¬ p664) ∨ (¬ p928) ∨ (¬ p1036)) : p14 ∨ p12 ∨ (¬ p664) ∨ p918 ∨ (¬ p87) ∨ (¬ p47) ∨ (¬ p189) ∨ (¬ p158) ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19590 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u10)

theorem step33040 (p12 p14 p15 p69 p86 p185 p229 p237 p664 p836 p840 p1036 : Prop)
    (h26849 : p229 ∨ p14)
    (h26907 : p1036 ∨ p12)
    (h26833 : p69 ∨ p15)
    (h26851 : p237 ∨ p185)
    (h26895 : p840 ∨ p836)
    (h18814 : (¬ p69) ∨ (¬ p86) ∨ (¬ p229) ∨ (¬ p237) ∨ (¬ p664) ∨ (¬ p840) ∨ (¬ p1036)) : p14 ∨ p12 ∨ p15 ∨ p185 ∨ p836 ∨ (¬ p86) ∨ (¬ p664) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18814 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u8)

theorem step33041 (p1 p12 p419 p663 p996 p1036 : Prop)
    (h26907 : p1036 ∨ p12)
    (h26905 : p996 ∨ p419)
    (h13072 : (¬ p1) ∨ (¬ p663) ∨ (¬ p996) ∨ (¬ p1036)) : (¬ p663) ∨ p12 ∨ p419 ∨ (¬ p1) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p663 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h13072 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step33042 (p12 p234 p541 p884 p1036 p1095 p1187 : Prop)
    (h26907 : p1036 ∨ p12)
    (h26921 : p1187 ∨ p234)
    (h17182 : (¬ p541) ∨ (¬ p884) ∨ (¬ p1036) ∨ (¬ p1095) ∨ (¬ p1187)) : (¬ p541) ∨ (¬ p1095) ∨ p12 ∨ (¬ p884) ∨ p234 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p541 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p884 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17182 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)

theorem step33043 (p3 p6 p12 p127 p226 p1036 p1076 p1077 : Prop)
    (h26847 : p226 ∨ p3)
    (h26839 : p127 ∨ p6)
    (h26911 : p1077 ∨ p1076)
    (h26907 : p1036 ∨ p12)
    (h19339 : (¬ p127) ∨ (¬ p226) ∨ (¬ p1036) ∨ (¬ p1077)) : p3 ∨ p6 ∨ p1076 ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19339 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)

theorem step33074 (p419 p996 p998 p1010 p1011 p1012 p1013 p1014 : Prop)
    (h26904 : (¬ p419) ∨ (¬ p996))
    (h5870 : p996 ∨ p998 ∨ (¬ p1010) ∨ (¬ p1011) ∨ (¬ p1012) ∨ (¬ p1013) ∨ (¬ p1014)) : (¬ p1011) ∨ (¬ p1010) ∨ (¬ p419) ∨ (¬ p1013) ∨ (¬ p1014) ∨ (¬ p1012) ∨ p998 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1011 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1010 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1013 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1014 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1012 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p998) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p996) := by
    rcases h26904 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h5870 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)

theorem step33078 (p17 p86 p126 p161 p256 p434 p1229 p1232 p1330 : Prop)
    (h26853 : p256 ∨ p17)
    (h26927 : p1232 ∨ p1229)
    (h16990 : (¬ p86) ∨ (¬ p126) ∨ (¬ p161) ∨ (¬ p256) ∨ (¬ p434) ∨ (¬ p1232) ∨ (¬ p1330)) : (¬ p434) ∨ p17 ∨ (¬ p1330) ∨ (¬ p161) ∨ (¬ p126) ∨ p1229 ∨ (¬ p86) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h16990 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u2)

theorem step33079 (p86 p161 p389 p789 p790 p1229 p1232 p1452 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h19687 : (¬ p86) ∨ (¬ p161) ∨ (¬ p389) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1232) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p789) ∨ (¬ p389) ∨ (¬ p790) ∨ p1229 ∨ (¬ p86) ∨ (¬ p161) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19687 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u0)

theorem step33080 (p86 p161 p189 p193 p422 p1000 p1229 p1232 p1256 p1325 p1333 : Prop)
    (h26929 : p1256 ∨ p422)
    (h26931 : p1333 ∨ p1325)
    (h26927 : p1232 ∨ p1229)
    (h26845 : p193 ∨ p189)
    (h18788 : (¬ p86) ∨ (¬ p161) ∨ (¬ p193) ∨ (¬ p1000) ∨ (¬ p1232) ∨ (¬ p1256) ∨ (¬ p1333)) : p422 ∨ p1325 ∨ p1229 ∨ (¬ p86) ∨ (¬ p161) ∨ (¬ p1000) ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p422) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18788 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)

theorem step33081 (p63 p161 p980 p983 p1229 p1232 : Prop)
    (h26903 : p983 ∨ p980)
    (h26927 : p1232 ∨ p1229)
    (h18128 : (¬ p63) ∨ (¬ p161) ∨ (¬ p983) ∨ (¬ p1232)) : p980 ∨ p1229 ∨ (¬ p161) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18128 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step33082 (p458 p495 p499 p532 p1229 p1232 p1325 p1333 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h26931 : p1333 ∨ p1325)
    (h26875 : p499 ∨ p495)
    (h18747 : (¬ p458) ∨ (¬ p499) ∨ (¬ p532) ∨ (¬ p1232) ∨ (¬ p1333)) : (¬ p458) ∨ p1229 ∨ p1325 ∨ p495 ∨ (¬ p532) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p458 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18747 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step33083 (p86 p161 p185 p237 p728 p836 p840 p1229 p1232 p1330 : Prop)
    (h26851 : p237 ∨ p185)
    (h26927 : p1232 ∨ p1229)
    (h26895 : p840 ∨ p836)
    (h17016 : (¬ p86) ∨ (¬ p161) ∨ (¬ p237) ∨ (¬ p728) ∨ (¬ p840) ∨ (¬ p1232) ∨ (¬ p1330)) : (¬ p728) ∨ p185 ∨ (¬ p161) ∨ p1229 ∨ p836 ∨ (¬ p86) ∨ (¬ p1330) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17016 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u6)

theorem step33084 (p86 p161 p189 p193 p424 p1229 p1232 p1330 p1366 : Prop)
    (h26845 : p193 ∨ p189)
    (h26927 : p1232 ∨ p1229)
    (h17541 : (¬ p86) ∨ (¬ p161) ∨ (¬ p193) ∨ (¬ p424) ∨ (¬ p1232) ∨ (¬ p1330) ∨ (¬ p1366)) : (¬ p1366) ∨ p189 ∨ (¬ p86) ∨ (¬ p161) ∨ (¬ p424) ∨ (¬ p1330) ∨ p1229 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17541 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u0)

theorem step33085 (p8 p63 p161 p728 p924 p1098 p1229 p1232 p1330 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h18460 : (¬ p8) ∨ (¬ p63) ∨ (¬ p161) ∨ (¬ p728) ∨ (¬ p924) ∨ (¬ p1098) ∨ (¬ p1232) ∨ (¬ p1330)) : (¬ p1098) ∨ (¬ p8) ∨ (¬ p161) ∨ (¬ p728) ∨ (¬ p924) ∨ p1229 ∨ (¬ p1330) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1098 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18460 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u6)

theorem step33087 (p15 p18 p69 p101 p285 p1055 p1061 p1115 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26833 : p69 ∨ p15)
    (h22795 : (¬ p1115) ∨ (¬ p285) ∨ (¬ p1061) ∨ (¬ p101) ∨ (¬ p69) ∨ (¬ p18)) : p1055 ∨ (¬ p1115) ∨ p15 ∨ (¬ p101) ∨ (¬ p18) ∨ (¬ p285) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1055) := fun hu => hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p285 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h22795 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u4)

theorem step33088 (p10 p38 p49 p84 p101 p125 p206 p242 p323 p836 p840 p1055 p1061 p1115 : Prop)
    (h26895 : p840 ∨ p836)
    (h26861 : p323 ∨ p10)
    (h26909 : p1061 ∨ p1055)
    (h20117 : (¬ p38) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p101) ∨ (¬ p125) ∨ (¬ p206) ∨ (¬ p242) ∨ (¬ p323) ∨ (¬ p840) ∨ (¬ p1061) ∨ (¬ p1115)) : (¬ p38) ∨ (¬ p125) ∨ (¬ p206) ∨ p836 ∨ p10 ∨ (¬ p101) ∨ (¬ p242) ∨ (¬ p84) ∨ (¬ p49) ∨ p1055 ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
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
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u12 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u13 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h20117 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u12)
  · exact False.elim (q8 u11)
  · exact False.elim (q9 u13)
  · exact False.elim (q10 u10)

theorem step33091 (p12 p18 p109 p884 p1036 p1095 : Prop)
    (h26907 : p1036 ∨ p12)
    (h17167 : (¬ p18) ∨ (¬ p109) ∨ (¬ p884) ∨ (¬ p1036) ∨ (¬ p1095)) : (¬ p1095) ∨ (¬ p109) ∨ (¬ p884) ∨ p12 ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p884 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17167 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step33092 (p50 p163 p167 p560 p884 p1055 p1095 : Prop)
    (h26843 : p167 ∨ p163)
    (h17040 : (¬ p50) ∨ (¬ p167) ∨ (¬ p560) ∨ (¬ p884) ∨ (¬ p1055) ∨ (¬ p1095)) : (¬ p560) ∨ (¬ p1055) ∨ (¬ p50) ∨ (¬ p1095) ∨ (¬ p884) ∨ p163 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p50 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p884 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17040 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u3)

theorem step33093 (p8 p50 p163 p167 p560 p710 p884 p897 p904 : Prop)
    (h26889 : p710 ∨ p8)
    (h26843 : p167 ∨ p163)
    (h26899 : p904 ∨ p897)
    (h17018 : (¬ p50) ∨ (¬ p167) ∨ (¬ p560) ∨ (¬ p710) ∨ (¬ p884) ∨ (¬ p904)) : p8 ∨ (¬ p884) ∨ p163 ∨ p897 ∨ (¬ p560) ∨ (¬ p50) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p8) := fun hu => hn (Or.inl hu)
  have u1 : p884 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p50 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17018 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u8)

theorem step33095 (p1 p12 p419 p663 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h14255 : (¬ p1) ∨ p12 ∨ (¬ p663) ∨ (¬ p996)) : (¬ p663) ∨ p12 ∨ p419 ∨ (¬ p1) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p663 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h14255 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step33096 (p3 p12 p25 p67 p226 p640 p1036 p1095 : Prop)
    (h26847 : p226 ∨ p3)
    (h26907 : p1036 ∨ p12)
    (h16612 : (¬ p25) ∨ (¬ p67) ∨ (¬ p226) ∨ (¬ p640) ∨ (¬ p1036) ∨ (¬ p1095)) : (¬ p25) ∨ (¬ p1095) ∨ (¬ p67) ∨ p3 ∨ (¬ p640) ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p25 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p640 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h16612 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u1)

theorem step33097 (p12 p25 p50 p163 p167 p640 p1036 p1095 : Prop)
    (h26907 : p1036 ∨ p12)
    (h26843 : p167 ∨ p163)
    (h16937 : (¬ p25) ∨ (¬ p50) ∨ (¬ p167) ∨ (¬ p640) ∨ (¬ p1036) ∨ (¬ p1095)) : p12 ∨ p163 ∨ (¬ p1095) ∨ (¬ p25) ∨ (¬ p640) ∨ (¬ p50) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p12) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p25 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p640 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p50 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16937 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)

theorem step33098 (p101 p344 p346 p640 p897 p904 : Prop)
    (h26899 : p904 ∨ p897)
    (h26863 : p346 ∨ p344)
    (h26246 : (¬ p904) ∨ (¬ p101) ∨ (¬ p640) ∨ (¬ p346)) : (¬ p101) ∨ (¬ p640) ∨ p897 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p640 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h26246 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)

theorem step33099 (p63 p344 p577 p595 p616 p640 p906 p1076 p1095 : Prop)
    (h26883 : p616 ∨ p595)
    (h17602 : (¬ p63) ∨ (¬ p344) ∨ (¬ p577) ∨ (¬ p616) ∨ (¬ p640) ∨ (¬ p906) ∨ (¬ p1076) ∨ (¬ p1095)) : (¬ p906) ∨ (¬ p1095) ∨ (¬ p344) ∨ p595 ∨ (¬ p577) ∨ (¬ p640) ∨ (¬ p1076) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p906 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p640 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17602 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u1)

theorem step33102 (p14 p17 p89 p229 p256 p560 p576 p980 p983 p1056 p1120 p1226 p1273 : Prop)
    (h26853 : p256 ∨ p17)
    (h26903 : p983 ∨ p980)
    (h26849 : p229 ∨ p14)
    (h19405 : (¬ p89) ∨ (¬ p229) ∨ (¬ p256) ∨ (¬ p560) ∨ (¬ p576) ∨ (¬ p983) ∨ (¬ p1056) ∨ (¬ p1120) ∨ (¬ p1226) ∨ (¬ p1273)) : p17 ∨ (¬ p1226) ∨ (¬ p1120) ∨ (¬ p1273) ∨ (¬ p1056) ∨ (¬ p560) ∨ p980 ∨ (¬ p89) ∨ p14 ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p17) := fun hu => hn (Or.inl hu)
  have u1 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1056 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u11 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u12 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h19405 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u12)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u1)
  · exact False.elim (q9 u3)

theorem step33105 (p121 p461 p495 p1206 p1229 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26247 : (¬ p1229) ∨ (¬ p1206) ∨ (¬ p461) ∨ (¬ p495)) : p121 ∨ (¬ p461) ∨ (¬ p495) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p461 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h26247 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)

theorem step33107 (p20 p137 p258 p288 p423 p633 p636 p1213 : Prop)
    (h26855 : p288 ∨ p258)
    (h26885 : p636 ∨ p633)
    (h16865 : (¬ p20) ∨ (¬ p137) ∨ (¬ p288) ∨ (¬ p423) ∨ (¬ p636) ∨ (¬ p1213)) : p258 ∨ (¬ p423) ∨ p633 ∨ (¬ p137) ∨ (¬ p1213) ∨ (¬ p20) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p258) := fun hu => hn (Or.inl hu)
  have u1 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p633) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p137 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p20 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16865 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u4)

theorem step33108 (p20 p137 p234 p258 p288 p330 p633 p636 : Prop)
    (h26855 : p288 ∨ p258)
    (h26885 : p636 ∨ p633)
    (h16883 : (¬ p20) ∨ (¬ p137) ∨ (¬ p234) ∨ (¬ p288) ∨ (¬ p330) ∨ (¬ p636)) : p258 ∨ p633 ∨ (¬ p137) ∨ (¬ p20) ∨ (¬ p330) ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p258) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p633) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p137 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p20 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16883 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)

theorem step33109 (p6 p127 p137 p163 p167 p195 p258 p288 p344 p560 p727 p769 : Prop)
    (h26843 : p167 ∨ p163)
    (h26855 : p288 ∨ p258)
    (h26839 : p127 ∨ p6)
    (h17410 : (¬ p127) ∨ (¬ p137) ∨ (¬ p167) ∨ (¬ p195) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p560) ∨ (¬ p727) ∨ (¬ p769)) : (¬ p769) ∨ p163 ∨ (¬ p344) ∨ p258 ∨ (¬ p195) ∨ p6 ∨ (¬ p560) ∨ (¬ p137) ∨ (¬ p727) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p137 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p727 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17410 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u11)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u0)

theorem step33110 (p6 p41 p127 p137 p195 p576 : Prop)
    (h26839 : p127 ∨ p6)
    (h20370 : (¬ p41) ∨ (¬ p127) ∨ (¬ p137) ∨ (¬ p195) ∨ (¬ p576)) : (¬ p137) ∨ (¬ p576) ∨ (¬ p195) ∨ (¬ p41) ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p137 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20370 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u1)

theorem step33111 (p6 p127 p136 p424 p1644 p1665 : Prop)
    (h26839 : p127 ∨ p6)
    (h17817 : (¬ p127) ∨ (¬ p136) ∨ (¬ p424) ∨ (¬ p1644) ∨ (¬ p1665)) : (¬ p1644) ∨ (¬ p136) ∨ (¬ p1665) ∨ p6 ∨ (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p136 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17817 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u2)

theorem step33112 (p6 p10 p126 p127 p136 p195 p301 p323 : Prop)
    (h26857 : p301 ∨ p126)
    (h26839 : p127 ∨ p6)
    (h26861 : p323 ∨ p10)
    (h17007 : (¬ p127) ∨ (¬ p136) ∨ (¬ p195) ∨ (¬ p301) ∨ (¬ p323)) : p126 ∨ p6 ∨ p10 ∨ (¬ p136) ∨ (¬ p195) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p136 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17007 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)

theorem step33113 (p15 p18 p69 p124 p136 p258 p330 p424 p496 : Prop)
    (h26833 : p69 ∨ p15)
    (h18816 : (¬ p18) ∨ (¬ p69) ∨ (¬ p124) ∨ (¬ p136) ∨ (¬ p258) ∨ (¬ p330) ∨ (¬ p424) ∨ (¬ p496)) : (¬ p258) ∨ (¬ p18) ∨ (¬ p330) ∨ (¬ p496) ∨ p15 ∨ (¬ p124) ∨ (¬ p424) ∨ (¬ p136) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p136 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18816 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u3)

theorem step33115 (p6 p23 p127 : Prop)
    (h26839 : p127 ∨ p6)
    (h17906 : p23 ∨ (¬ p127)) : p23 ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p23) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr hu)
  have u2 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17906 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)

theorem step33117 (p6 p86 p127 p134 p186 p424 p542 p897 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26839 : p127 ∨ p6)
    (h16926 : (¬ p86) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p186) ∨ (¬ p424) ∨ (¬ p542) ∨ (¬ p897) ∨ (¬ p1099)) : (¬ p424) ∨ (¬ p134) ∨ p1096 ∨ (¬ p186) ∨ (¬ p86) ∨ (¬ p542) ∨ p6 ∨ (¬ p897) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h16926 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u8)

theorem step33118 (p6 p86 p127 p134 p186 p382 p424 p614 p1195 p1286 : Prop)
    (h26839 : p127 ∨ p6)
    (h16940 : (¬ p86) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p186) ∨ (¬ p382) ∨ (¬ p424) ∨ (¬ p614) ∨ (¬ p1195) ∨ (¬ p1286)) : (¬ p1195) ∨ (¬ p186) ∨ p6 ∨ (¬ p1286) ∨ (¬ p382) ∨ (¬ p134) ∨ (¬ p86) ∨ (¬ p614) ∨ (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p614 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16940 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u3)

theorem step33119 (p6 p86 p127 p134 p186 p422 p595 p616 p1000 p1256 p1287 : Prop)
    (h26929 : p1256 ∨ p422)
    (h26883 : p616 ∨ p595)
    (h26839 : p127 ∨ p6)
    (h16955 : (¬ p86) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p186) ∨ (¬ p616) ∨ (¬ p1000) ∨ (¬ p1256) ∨ (¬ p1287)) : p422 ∨ (¬ p134) ∨ (¬ p86) ∨ (¬ p1287) ∨ (¬ p1000) ∨ p595 ∨ (¬ p186) ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p422) := fun hu => hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h16955 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u3)

theorem step33121 (p6 p10 p84 p127 p186 p323 p434 p929 p980 p1055 p1102 p1330 : Prop)
    (h26839 : p127 ∨ p6)
    (h26861 : p323 ∨ p10)
    (h16976 : (¬ p84) ∨ (¬ p127) ∨ (¬ p186) ∨ (¬ p323) ∨ (¬ p434) ∨ (¬ p929) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1102) ∨ (¬ p1330)) : (¬ p434) ∨ (¬ p186) ∨ p6 ∨ p10 ∨ (¬ p1102) ∨ (¬ p1330) ∨ (¬ p929) ∨ (¬ p84) ∨ (¬ p1055) ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16976 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u4)
  · exact False.elim (q9 u5)

theorem step33124 (p6 p10 p86 p127 p186 p303 p323 p387 p431 p595 p616 p1545 : Prop)
    (h26883 : p616 ∨ p595)
    (h26861 : p323 ∨ p10)
    (h26839 : p127 ∨ p6)
    (h26867 : p387 ∨ p303)
    (h17001 : (¬ p86) ∨ (¬ p127) ∨ (¬ p186) ∨ (¬ p323) ∨ (¬ p387) ∨ (¬ p431) ∨ (¬ p616) ∨ (¬ p1545)) : (¬ p431) ∨ (¬ p1545) ∨ p595 ∨ p10 ∨ p6 ∨ p303 ∨ (¬ p86) ∨ (¬ p186) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17001 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u1)

theorem step33125 (p3 p6 p18 p127 p226 p940 : Prop)
    (h26847 : p226 ∨ p3)
    (h26839 : p127 ∨ p6)
    (h17229 : (¬ p18) ∨ (¬ p127) ∨ (¬ p226) ∨ (¬ p940)) : p3 ∨ p6 ∨ (¬ p940) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17229 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step33126 (p6 p127 p455 p1140 p1159 p1208 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26839 : p127 ∨ p6)
    (h26248 : (¬ p1208) ∨ (¬ p1159) ∨ (¬ p127) ∨ (¬ p455)) : (¬ p1208) ∨ p1140 ∨ (¬ p455) ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1208 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1140) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h26248 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)

theorem step33127 (p6 p18 p127 p419 p1193 p1286 : Prop)
    (h26839 : p127 ∨ p6)
    (h17759 : (¬ p18) ∨ (¬ p127) ∨ (¬ p419) ∨ (¬ p1193) ∨ (¬ p1286)) : (¬ p1193) ∨ (¬ p18) ∨ (¬ p419) ∨ p6 ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17759 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)

theorem step33128 (p6 p18 p127 p171 p185 p187 p234 p237 p790 p803 p814 : Prop)
    (h26839 : p127 ∨ p6)
    (h26851 : p237 ∨ p185)
    (h26893 : p814 ∨ p790)
    (h17774 : (¬ p18) ∨ (¬ p127) ∨ (¬ p171) ∨ (¬ p187) ∨ (¬ p234) ∨ (¬ p237) ∨ (¬ p803) ∨ (¬ p814)) : (¬ p171) ∨ p6 ∨ (¬ p18) ∨ (¬ p234) ∨ p185 ∨ (¬ p803) ∨ (¬ p187) ∨ p790 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p803 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h17774 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u10)

theorem step33129 (p6 p18 p127 p234 p303 p328 p387 : Prop)
    (h26867 : p387 ∨ p303)
    (h26839 : p127 ∨ p6)
    (h17866 : (¬ p18) ∨ (¬ p127) ∨ (¬ p234) ∨ (¬ p328) ∨ (¬ p387)) : p303 ∨ p6 ∨ (¬ p18) ∨ (¬ p234) ∨ (¬ p328) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p328 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17866 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step33130 (p6 p18 p127 p172 p185 p187 p234 p539 p790 : Prop)
    (h26839 : p127 ∨ p6)
    (h26249 : (¬ p790) ∨ (¬ p127) ∨ (¬ p234) ∨ (¬ p172) ∨ (¬ p185) ∨ (¬ p18) ∨ (¬ p539) ∨ (¬ p187)) : p6 ∨ (¬ p18) ∨ (¬ p185) ∨ (¬ p172) ∨ (¬ p539) ∨ (¬ p234) ∨ (¬ p790) ∨ (¬ p187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p539 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h26249 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step33131 (p6 p18 p127 p234 p344 p346 p543 : Prop)
    (h26839 : p127 ∨ p6)
    (h26863 : p346 ∨ p344)
    (h17877 : (¬ p18) ∨ (¬ p127) ∨ (¬ p234) ∨ (¬ p346) ∨ (¬ p543)) : p6 ∨ (¬ p543) ∨ (¬ p18) ∨ (¬ p234) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : p543 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17877 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)

theorem step33132 (p6 p63 p127 p134 p918 p928 p1044 p1115 p1116 p1140 p1159 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26901 : p928 ∨ p918)
    (h26915 : p1116 ∨ p1115)
    (h26839 : p127 ∨ p6)
    (h18627 : (¬ p63) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p928) ∨ (¬ p1044) ∨ (¬ p1116) ∨ (¬ p1159)) : p1140 ∨ p918 ∨ p1115 ∨ (¬ p134) ∨ (¬ p63) ∨ (¬ p1044) ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18627 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u7)

theorem step33133 (p3 p6 p18 p127 p163 p226 : Prop)
    (h26847 : p226 ∨ p3)
    (h26839 : p127 ∨ p6)
    (h19128 : (¬ p18) ∨ (¬ p127) ∨ (¬ p163) ∨ (¬ p226)) : p3 ∨ p6 ∨ (¬ p163) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19128 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step33134 (p6 p18 p127 p224 p234 p241 p382 p542 p657 p709 p918 : Prop)
    (h26839 : p127 ∨ p6)
    (h26887 : p657 ∨ p224)
    (h20326 : (¬ p18) ∨ (¬ p127) ∨ (¬ p234) ∨ (¬ p241) ∨ (¬ p382) ∨ (¬ p542) ∨ (¬ p657) ∨ (¬ p709) ∨ (¬ p918)) : (¬ p918) ∨ (¬ p18) ∨ (¬ p709) ∨ (¬ p382) ∨ p6 ∨ (¬ p234) ∨ (¬ p542) ∨ (¬ p241) ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h20326 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u0)

theorem step33135 (p6 p18 p127 p234 p1366 : Prop)
    (h26839 : p127 ∨ p6)
    (h20332 : (¬ p18) ∨ (¬ p127) ∨ (¬ p234) ∨ (¬ p1366)) : (¬ p1366) ∨ p6 ∨ (¬ p234) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20332 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)

theorem step33136 (p6 p8 p18 p127 p224 p241 p423 p710 p918 p1000 : Prop)
    (h26839 : p127 ∨ p6)
    (h26889 : p710 ∨ p8)
    (h20337 : (¬ p18) ∨ (¬ p127) ∨ (¬ p224) ∨ (¬ p241) ∨ (¬ p423) ∨ (¬ p710) ∨ (¬ p918) ∨ (¬ p1000)) : (¬ p1000) ∨ p6 ∨ p8 ∨ (¬ p423) ∨ (¬ p224) ∨ (¬ p18) ∨ (¬ p241) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20337 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u0)

theorem step33137 (p3 p6 p18 p127 p225 p226 : Prop)
    (h26847 : p226 ∨ p3)
    (h26839 : p127 ∨ p6)
    (h20570 : (¬ p18) ∨ (¬ p127) ∨ (¬ p225) ∨ (¬ p226)) : p3 ∨ p6 ∨ (¬ p225) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20570 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step33138 (p6 p18 p127 p234 p419 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26839 : p127 ∨ p6)
    (h20583 : (¬ p18) ∨ (¬ p127) ∨ (¬ p234) ∨ (¬ p996)) : p419 ∨ p6 ∨ (¬ p18) ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20583 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step33139 (p6 p21 p127 p241 p420 p434 p601 p918 p980 p1055 p1330 : Prop)
    (h26839 : p127 ∨ p6)
    (h26881 : p601 ∨ p420)
    (h20584 : (¬ p21) ∨ (¬ p127) ∨ (¬ p241) ∨ (¬ p434) ∨ (¬ p601) ∨ (¬ p918) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1330)) : (¬ p241) ∨ (¬ p434) ∨ (¬ p1055) ∨ (¬ p918) ∨ (¬ p1330) ∨ p6 ∨ (¬ p21) ∨ p420 ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20584 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u4)

theorem step33140 (p6 p18 p127 p241 p423 p918 p980 p983 p1040 p1056 p1226 : Prop)
    (h26903 : p983 ∨ p980)
    (h26839 : p127 ∨ p6)
    (h20586 : (¬ p18) ∨ (¬ p127) ∨ (¬ p241) ∨ (¬ p423) ∨ (¬ p918) ∨ (¬ p983) ∨ (¬ p1040) ∨ (¬ p1056) ∨ (¬ p1226)) : (¬ p18) ∨ p980 ∨ (¬ p241) ∨ (¬ p1226) ∨ (¬ p1056) ∨ (¬ p918) ∨ (¬ p423) ∨ p6 ∨ (¬ p1040) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1056 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1040 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20586 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u3)

theorem step33141 (p6 p18 p127 p325 p349 p477 p690 p1366 : Prop)
    (h26839 : p127 ∨ p6)
    (h20625 : (¬ p18) ∨ (¬ p127) ∨ (¬ p325) ∨ (¬ p349) ∨ (¬ p477) ∨ (¬ p690) ∨ (¬ p1366)) : (¬ p325) ∨ (¬ p1366) ∨ (¬ p477) ∨ (¬ p349) ∨ (¬ p690) ∨ p6 ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p477 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20625 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u1)

theorem step33142 (p6 p18 p127 p1140 p1159 p1465 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26839 : p127 ∨ p6)
    (h20627 : (¬ p18) ∨ (¬ p127) ∨ (¬ p1159) ∨ (¬ p1465)) : p1140 ∨ p6 ∨ (¬ p1465) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20627 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step33143 (p6 p18 p127 p224 p657 p897 p904 p1004 p1096 p1140 p1159 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26887 : p657 ∨ p224)
    (h26839 : p127 ∨ p6)
    (h26899 : p904 ∨ p897)
    (h20629 : (¬ p18) ∨ (¬ p127) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1004) ∨ (¬ p1096) ∨ (¬ p1159)) : p1140 ∨ (¬ p1004) ∨ (¬ p18) ∨ p224 ∨ p6 ∨ p897 ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20629 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step33145 (p2 p6 p127 p325 p420 p601 : Prop)
    (h26839 : p127 ∨ p6)
    (h26881 : p601 ∨ p420)
    (h26250 : (¬ p325) ∨ (¬ p601) ∨ (¬ p127) ∨ (¬ p2)) : (¬ p325) ∨ (¬ p2) ∨ p6 ∨ p420 := by
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
  have u3 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h26250 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)

theorem step33146 (p2 p6 p18 p127 p424 : Prop)
    (h26839 : p127 ∨ p6)
    (h19014 : (¬ p2) ∨ (¬ p18) ∨ (¬ p127) ∨ (¬ p424)) : (¬ p2) ∨ p6 ∨ (¬ p18) ∨ (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19014 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)

theorem step33147 (p2 p6 p18 p127 p435 : Prop)
    (h26839 : p127 ∨ p6)
    (h20631 : (¬ p2) ∨ (¬ p18) ∨ (¬ p127) ∨ (¬ p435)) : (¬ p2) ∨ p6 ∨ (¬ p18) ∨ (¬ p435) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20631 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)

theorem step33150 (p6 p10 p39 p63 p68 p127 p303 p323 p387 p1229 p1232 p1295 : Prop)
    (h26867 : p387 ∨ p303)
    (h26839 : p127 ∨ p6)
    (h26861 : p323 ∨ p10)
    (h26927 : p1232 ∨ p1229)
    (h17604 : (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p127) ∨ (¬ p323) ∨ (¬ p387) ∨ (¬ p1232) ∨ (¬ p1295)) : (¬ p1295) ∨ p303 ∨ (¬ p68) ∨ p6 ∨ (¬ p63) ∨ p10 ∨ (¬ p39) ∨ p1229 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1295 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h17604 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u0)

theorem step33152 (p6 p21 p72 p127 p234 p303 p387 p420 p431 p435 p601 p1187 : Prop)
    (h26867 : p387 ∨ p303)
    (h26839 : p127 ∨ p6)
    (h26921 : p1187 ∨ p234)
    (h26881 : p601 ∨ p420)
    (h17876 : (¬ p21) ∨ (¬ p72) ∨ (¬ p127) ∨ (¬ p387) ∨ (¬ p431) ∨ (¬ p435) ∨ (¬ p601) ∨ (¬ p1187)) : (¬ p431) ∨ p303 ∨ (¬ p21) ∨ (¬ p435) ∨ (¬ p72) ∨ p6 ∨ p234 ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h17876 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u10)

theorem step33153 (p6 p21 p72 p127 p234 p382 p420 p434 p480 p601 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26881 : p601 ∨ p420)
    (h26839 : p127 ∨ p6)
    (h26252 : (¬ p1187) ∨ (¬ p601) ∨ (¬ p127) ∨ (¬ p72) ∨ (¬ p480) ∨ (¬ p382) ∨ (¬ p434) ∨ (¬ p21)) : p234 ∨ (¬ p434) ∨ p420 ∨ p6 ∨ (¬ p480) ∨ (¬ p382) ∨ (¬ p72) ∨ (¬ p21) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p480 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h26252 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u7)

theorem step33154 (p6 p10 p20 p72 p127 p323 p420 : Prop)
    (h26839 : p127 ∨ p6)
    (h26861 : p323 ∨ p10)
    (h19054 : (¬ p20) ∨ (¬ p72) ∨ (¬ p127) ∨ (¬ p323) ∨ (¬ p420)) : (¬ p420) ∨ p6 ∨ (¬ p72) ∨ p10 ∨ (¬ p20) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p20 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19054 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)

theorem step33155 (p6 p21 p72 p127 p224 p234 p347 p382 p420 p480 p601 p657 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26881 : p601 ∨ p420)
    (h26839 : p127 ∨ p6)
    (h26887 : p657 ∨ p224)
    (h19086 : (¬ p21) ∨ (¬ p72) ∨ (¬ p127) ∨ (¬ p347) ∨ (¬ p382) ∨ (¬ p480) ∨ (¬ p601) ∨ (¬ p657) ∨ (¬ p1187)) : p234 ∨ (¬ p382) ∨ p420 ∨ (¬ p480) ∨ (¬ p21) ∨ p6 ∨ (¬ p72) ∨ (¬ p347) ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p480 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u12 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h19086 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u12)
  · exact False.elim (q8 u9)

theorem step33156 (p6 p14 p21 p72 p127 p229 p344 p560 p633 p664 p1055 : Prop)
    (h26849 : p229 ∨ p14)
    (h26839 : p127 ∨ p6)
    (h19314 : (¬ p21) ∨ (¬ p72) ∨ (¬ p127) ∨ (¬ p229) ∨ (¬ p344) ∨ (¬ p560) ∨ (¬ p633) ∨ (¬ p664) ∨ (¬ p1055)) : p14 ∨ (¬ p21) ∨ p6 ∨ (¬ p560) ∨ (¬ p72) ∨ (¬ p664) ∨ (¬ p344) ∨ (¬ p1055) ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19314 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u7)

theorem step33157 (p6 p21 p72 p127 p423 p533 p633 p756 p1141 p1167 p1226 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26839 : p127 ∨ p6)
    (h19622 : (¬ p21) ∨ (¬ p72) ∨ (¬ p127) ∨ (¬ p533) ∨ (¬ p633) ∨ (¬ p756) ∨ (¬ p1141) ∨ (¬ p1167) ∨ (¬ p1226)) : p423 ∨ (¬ p1167) ∨ (¬ p72) ∨ p6 ∨ (¬ p1226) ∨ (¬ p21) ∨ (¬ p633) ∨ (¬ p533) ∨ (¬ p756) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p1167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19622 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u4)

theorem step33159 (p2 p6 p18 p89 p127 p185 p224 p237 p545 p789 p839 : Prop)
    (h26839 : p127 ∨ p6)
    (h26851 : p237 ∨ p185)
    (h20634 : (¬ p2) ∨ (¬ p18) ∨ (¬ p89) ∨ (¬ p127) ∨ (¬ p224) ∨ (¬ p237) ∨ (¬ p545) ∨ (¬ p789) ∨ (¬ p839)) : (¬ p2) ∨ (¬ p224) ∨ (¬ p89) ∨ (¬ p18) ∨ (¬ p839) ∨ (¬ p545) ∨ p6 ∨ (¬ p789) ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p839 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h20634 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u4)

theorem step33161 (p6 p18 p68 p127 : Prop)
    (h26839 : p127 ∨ p6)
    (h646 : (¬ p18) ∨ (¬ p68) ∨ (¬ p127)) : p6 ∨ (¬ p18) ∨ (¬ p68) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h646 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step33164 (p6 p12 p108 p127 p344 p1076 : Prop)
    (h26839 : p127 ∨ p6)
    (h17852 : (¬ p12) ∨ (¬ p108) ∨ (¬ p127) ∨ (¬ p344) ∨ (¬ p1076)) : p6 ∨ (¬ p344) ∨ (¬ p108) ∨ (¬ p1076) ∨ (¬ p12) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17852 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)

theorem step33165 (p6 p20 p72 p101 p102 p127 p633 p636 : Prop)
    (h26885 : p636 ∨ p633)
    (h26839 : p127 ∨ p6)
    (h26837 : p102 ∨ p101)
    (h18597 : (¬ p20) ∨ (¬ p72) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p636)) : p633 ∨ p6 ∨ (¬ p20) ∨ (¬ p72) ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p20 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18597 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step33166 (p6 p39 p63 p68 p101 p102 p127 p344 p595 p616 p842 p1388 : Prop)
    (h26839 : p127 ∨ p6)
    (h26883 : p616 ∨ p595)
    (h26837 : p102 ∨ p101)
    (h17606 : (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p344) ∨ (¬ p616) ∨ (¬ p842) ∨ (¬ p1388)) : p6 ∨ (¬ p1388) ∨ (¬ p842) ∨ p595 ∨ (¬ p68) ∨ p101 ∨ (¬ p39) ∨ (¬ p344) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : p1388 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p842 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17606 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u1)

theorem step33168 (p6 p14 p18 p107 p127 p344 : Prop)
    (h26839 : p127 ∨ p6)
    (h17840 : (¬ p14) ∨ (¬ p18) ∨ (¬ p107) ∨ (¬ p127) ∨ (¬ p344)) : p6 ∨ (¬ p18) ∨ (¬ p344) ∨ (¬ p14) ∨ (¬ p107) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17840 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)

theorem step33169 (p6 p8 p18 p104 p127 p557 p667 p980 p983 p1004 p1140 p1159 p1325 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26839 : p127 ∨ p6)
    (h26903 : p983 ∨ p980)
    (h19887 : (¬ p8) ∨ (¬ p18) ∨ (¬ p104) ∨ (¬ p127) ∨ (¬ p557) ∨ (¬ p667) ∨ (¬ p983) ∨ (¬ p1004) ∨ (¬ p1159) ∨ (¬ p1325)) : (¬ p1004) ∨ p1140 ∨ (¬ p18) ∨ (¬ p557) ∨ (¬ p8) ∨ (¬ p104) ∨ (¬ p1325) ∨ (¬ p667) ∨ p6 ∨ p980 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1140) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u12 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h19887 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u12)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u6)

theorem step33170 (p3 p6 p63 p104 p126 p127 p134 p226 p350 p576 p581 : Prop)
    (h26847 : p226 ∨ p3)
    (h26839 : p127 ∨ p6)
    (h26879 : p581 ∨ p576)
    (h18632 : (¬ p63) ∨ (¬ p104) ∨ (¬ p126) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p226) ∨ (¬ p350) ∨ (¬ p581)) : p3 ∨ (¬ p134) ∨ (¬ p104) ∨ (¬ p63) ∨ (¬ p126) ∨ p6 ∨ p576 ∨ (¬ p350) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18632 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u10)

theorem step33223 (p15 p17 p18 p69 p86 p101 p126 p256 p350 : Prop)
    (h26833 : p69 ∨ p15)
    (h26853 : p256 ∨ p17)
    (h18468 : (¬ p18) ∨ (¬ p69) ∨ (¬ p86) ∨ (¬ p101) ∨ (¬ p126) ∨ (¬ p256) ∨ (¬ p350)) : (¬ p101) ∨ (¬ p350) ∨ (¬ p18) ∨ (¬ p126) ∨ p15 ∨ p17 ∨ (¬ p86) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u8 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18468 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u1)

theorem step33225 (p13 p15 p18 p69 p86 p121 p185 p237 p1115 p1116 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26851 : p237 ∨ p185)
    (h26915 : p1116 ∨ p1115)
    (h26833 : p69 ∨ p15)
    (h20311 : (¬ p13) ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p86) ∨ (¬ p237) ∨ (¬ p1116) ∨ (¬ p1206)) : (¬ p13) ∨ p121 ∨ (¬ p86) ∨ p185 ∨ p1115 ∨ p15 ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20311 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u7)

theorem step33227 (p15 p18 p63 p69 p101 : Prop)
    (h26833 : p69 ∨ p15)
    (h17954 : (¬ p18) ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p101)) : (¬ p101) ∨ p15 ∨ (¬ p63) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17954 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step33228 (p15 p18 p63 p69 p134 p142 : Prop)
    (h26833 : p69 ∨ p15)
    (h26841 : p142 ∨ p134)
    (h18046 : (¬ p18) ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p142)) : p15 ∨ (¬ p18) ∨ (¬ p63) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p15) := fun hu => hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18046 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step33229 (p15 p18 p63 p69 p124 p224 p344 p421 p577 p657 : Prop)
    (h26833 : p69 ∨ p15)
    (h26887 : p657 ∨ p224)
    (h18056 : (¬ p18) ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p124) ∨ (¬ p344) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p657)) : p15 ∨ (¬ p18) ∨ (¬ p421) ∨ (¬ p124) ∨ (¬ p577) ∨ (¬ p63) ∨ p224 ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p15) := fun hu => hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18056 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u9)

theorem step33230 (p6 p18 p63 p127 p789 p1004 p1140 p1159 p1385 p1393 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26839 : p127 ∨ p6)
    (h26933 : p1393 ∨ p1385)
    (h20623 : (¬ p18) ∨ (¬ p63) ∨ (¬ p127) ∨ (¬ p789) ∨ (¬ p1004) ∨ (¬ p1159) ∨ (¬ p1393)) : p1140 ∨ p6 ∨ (¬ p789) ∨ (¬ p1004) ∨ (¬ p18) ∨ p1385 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20623 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u9)

theorem step33253 (p15 p41 p47 p63 p85 p1249 : Prop)
    (h26835 : p85 ∨ p63)
    (h22545 : (¬ p1249) ∨ (¬ p15) ∨ (¬ p85) ∨ (¬ p47) ∨ (¬ p41)) : (¬ p1249) ∨ (¬ p15) ∨ p63 ∨ (¬ p47) ∨ (¬ p41) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h22545 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)

theorem step33254 (p303 p387 p595 p599 p616 p1229 p1232 : Prop)
    (h26867 : p387 ∨ p303)
    (h26927 : p1232 ∨ p1229)
    (h26882 : (¬ p595) ∨ (¬ p616))
    (h22609 : (¬ p1232) ∨ p616 ∨ (¬ p599) ∨ (¬ p387)) : p303 ∨ (¬ p599) ∨ p1229 ∨ (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p599 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : (¬ p616) := by
    rcases h26882 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h22609 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step33255 (p10 p24 p323 p495 p499 p633 p1096 p1099 : Prop)
    (h26875 : p499 ∨ p495)
    (h26913 : p1099 ∨ p1096)
    (h26861 : p323 ∨ p10)
    (h22633 : p633 ∨ (¬ p323) ∨ (¬ p499) ∨ (¬ p1099) ∨ (¬ p24)) : p633 ∨ (¬ p24) ∨ p495 ∨ p1096 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h22633 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)

theorem step33256 (p15 p69 p86 p185 p234 p237 p419 p1115 p1116 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26915 : p1116 ∨ p1115)
    (h26851 : p237 ∨ p185)
    (h26833 : p69 ∨ p15)
    (h22225 : (¬ p419) ∨ (¬ p237) ∨ (¬ p86) ∨ (¬ p1187) ∨ (¬ p1116) ∨ (¬ p69)) : p234 ∨ p1115 ∨ (¬ p419) ∨ (¬ p86) ∨ p185 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1115) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h22225 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u9)

theorem step33258 (p595 p616 p620 : Prop)
    (h26882 : (¬ p595) ∨ (¬ p616))
    (h22669 : p620 ∨ p616) : p620 ∨ (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p620) := fun hu => hn (Or.inl hu)
  have u1 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p616) := by
    rcases h26882 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h22669 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33259 (p15 p18 p19 p326 p595 : Prop)
    (h26829 : p19 ∨ p18)
    (h21791 : p595 ∨ (¬ p19) ∨ (¬ p326) ∨ (¬ p15)) : (¬ p15) ∨ p18 ∨ (¬ p326) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h21791 with q0 | q1 | q2 | q3
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)

theorem step33260 (p306 p350 p420 p601 p1055 p1061 p1076 p1077 p1095 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26881 : p601 ∨ p420)
    (h26909 : p1061 ∨ p1055)
    (h22312 : p1095 ∨ (¬ p350) ∨ (¬ p1061) ∨ (¬ p306) ∨ (¬ p1077) ∨ (¬ p601)) : p1076 ∨ (¬ p350) ∨ p420 ∨ p1095 ∨ (¬ p306) ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1095) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h22312 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)

theorem step33261 (p101 p124 p125 p304 p329 p350 p438 p1366 : Prop)
    (h26859 : p304 ∨ p124)
    (h21955 : p125 ∨ (¬ p438) ∨ (¬ p1366) ∨ (¬ p304) ∨ (¬ p350) ∨ (¬ p101) ∨ (¬ p329)) : (¬ p1366) ∨ (¬ p101) ∨ (¬ p350) ∨ (¬ p329) ∨ p124 ∨ (¬ p438) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p329 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h21955 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u3)

theorem step33262 (p10 p101 p121 p124 p125 p304 p350 p384 p419 p1206 p1366 : Prop)
    (h26859 : p304 ∨ p124)
    (h26923 : p1206 ∨ p121)
    (h22386 : (¬ p1366) ∨ (¬ p1206) ∨ (¬ p419) ∨ (¬ p101) ∨ (¬ p384) ∨ (¬ p350) ∨ p125 ∨ (¬ p304) ∨ p10) : (¬ p1366) ∨ (¬ p101) ∨ p10 ∨ p124 ∨ p121 ∨ (¬ p384) ∨ (¬ p350) ∨ (¬ p419) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p384 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h22386 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (u8 q6)
  · exact False.elim (q7 u9)
  · exact False.elim (u2 q8)

theorem step33263 (p21 p101 p350 p495 p595 p616 : Prop)
    (h26882 : (¬ p595) ∨ (¬ p616))
    (h22292 : p616 ∨ (¬ p101) ∨ (¬ p350) ∨ (¬ p495) ∨ (¬ p21)) : (¬ p101) ∨ (¬ p350) ∨ (¬ p21) ∨ (¬ p495) ∨ (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p616) := by
    rcases h26882 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  rcases h22292 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)

theorem step33264 (p6 p127 p206 : Prop)
    (h26838 : (¬ p6) ∨ (¬ p127))
    (h21764 : p127 ∨ p206) : (¬ p6) ∨ p206 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p206) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p127) := by
    rcases h26838 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h21764 with q0 | q1
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)

theorem step33268 (p15 p38 p69 : Prop)
    (h26832 : (¬ p15) ∨ (¬ p69))
    (h23956 : p69 ∨ p38) : (¬ p15) ∨ p38 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p38) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p69) := by
    rcases h26832 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h23956 with q0 | q1
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)

theorem step33269 (p258 p283 p288 : Prop)
    (h26854 : (¬ p258) ∨ (¬ p288))
    (h21864 : p283 ∨ p288) : p283 ∨ (¬ p258) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p283) := fun hu => hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p288) := by
    rcases h26854 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h21864 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33270 (p255 p258 p288 : Prop)
    (h26854 : (¬ p258) ∨ (¬ p288))
    (h22683 : p255 ∨ p288) : p255 ∨ (¬ p258) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p255) := fun hu => hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p288) := by
    rcases h26854 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h22683 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33274 (p3 p185 p192 p237 : Prop)
    (h26851 : p237 ∨ p185)
    (h22384 : p192 ∨ (¬ p237) ∨ p3) : p3 ∨ p185 ∨ p192 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p192) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h22384 with q0 | q1 | q2
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (u0 q2)

theorem step33275 (p189 p192 p193 : Prop)
    (h26845 : p193 ∨ p189)
    (h22057 : p192 ∨ (¬ p193)) : p192 ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p192) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr hu)
  have u2 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h22057 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)

theorem step33276 (p789 p858 p862 : Prop)
    (h26896 : (¬ p789) ∨ (¬ p858))
    (h21694 : p858 ∨ p862) : (¬ p789) ∨ p862 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p862) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p858) := by
    rcases h26896 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h21694 with q0 | q1
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)

theorem step33277 (p101 p121 p156 p185 p192 p206 p224 p657 p790 p961 : Prop)
    (h26887 : p657 ∨ p224)
    (h22218 : (¬ p790) ∨ (¬ p961) ∨ (¬ p156) ∨ (¬ p192) ∨ (¬ p121) ∨ (¬ p657) ∨ (¬ p185) ∨ (¬ p101) ∨ (¬ p206)) : (¬ p961) ∨ (¬ p185) ∨ (¬ p121) ∨ (¬ p206) ∨ (¬ p192) ∨ (¬ p156) ∨ (¬ p101) ∨ (¬ p790) ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h22218 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u3)

theorem step33280 (p101 p102 p258 p1076 p1077 p1115 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26837 : p102 ∨ p101)
    (h21867 : (¬ p102) ∨ (¬ p1115) ∨ (¬ p258) ∨ (¬ p1077)) : (¬ p1115) ∨ p1076 ∨ (¬ p258) ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h21867 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step33283 (p124 p304 p309 : Prop)
    (h26858 : (¬ p124) ∨ (¬ p304))
    (h22249 : p309 ∨ p304) : p309 ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p309) := fun hu => hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p304) := by
    rcases h26858 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h22249 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33284 (p124 p227 p304 p1055 p1061 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26858 : (¬ p124) ∨ (¬ p304))
    (h22644 : p227 ∨ p304 ∨ (¬ p1061)) : p227 ∨ p1055 ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p227) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u4 : (¬ p304) := by
    rcases h26858 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h22644 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u3)

theorem step33286 (p41 p185 p237 p382 p918 p1325 p1385 : Prop)
    (h26851 : p237 ∨ p185)
    (h22382 : (¬ p41) ∨ (¬ p1325) ∨ (¬ p1385) ∨ (¬ p918) ∨ (¬ p382) ∨ (¬ p237)) : (¬ p1385) ∨ (¬ p41) ∨ p185 ∨ (¬ p1325) ∨ (¬ p382) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h22382 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)

theorem step33289 (p11 p18 p121 p423 p1206 : Prop)
    (h26922 : (¬ p121) ∨ (¬ p1206))
    (h22822 : (¬ p423) ∨ p1206 ∨ (¬ p11) ∨ (¬ p18)) : (¬ p11) ∨ (¬ p423) ∨ (¬ p18) ∨ (¬ p121) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
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
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p1206) := by
    rcases h26922 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h22822 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)

theorem step33290 (p419 p996 p997 : Prop)
    (h26904 : (¬ p419) ∨ (¬ p996))
    (h21727 : p997 ∨ p996) : p997 ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p997) := fun hu => hn (Or.inl hu)
  have u1 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p996) := by
    rcases h26904 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h21727 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33291 (p224 p657 p662 : Prop)
    (h26886 : (¬ p224) ∨ (¬ p657))
    (h21721 : p662 ∨ p657) : p662 ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p662) := fun hu => hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p657) := by
    rcases h26886 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h21721 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33292 (p224 p657 p665 : Prop)
    (h26886 : (¬ p224) ∨ (¬ p657))
    (h22069 : p665 ∨ p657) : p665 ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p665) := fun hu => hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p657) := by
    rcases h26886 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h22069 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33296 (p15 p22 p125 p362 p420 p495 p499 p601 : Prop)
    (h26864 : (¬ p125) ∨ (¬ p362))
    (h26881 : p601 ∨ p420)
    (h26874 : (¬ p495) ∨ (¬ p499))
    (h22255 : p362 ∨ p499 ∨ (¬ p15) ∨ (¬ p601) ∨ (¬ p22)) : (¬ p15) ∨ (¬ p125) ∨ p420 ∨ (¬ p22) ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p22 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p362) := by
    rcases h26864 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u6 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : (¬ p499) := by
    rcases h26874 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  rcases h22255 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u5 q0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)

theorem step33298 (p124 p125 p362 p1055 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26865 : p362 ∨ p125)
    (h22256 : (¬ p362) ∨ (¬ p1055) ∨ p124 ∨ (¬ p1077)) : p124 ∨ p1076 ∨ p125 ∨ (¬ p1055) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h22256 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u4)

theorem step33301 (p41 p185 p224 p237 p657 p789 p858 p918 : Prop)
    (h26851 : p237 ∨ p185)
    (h26897 : p858 ∨ p789)
    (h26887 : p657 ∨ p224)
    (h22578 : (¬ p657) ∨ (¬ p858) ∨ (¬ p41) ∨ (¬ p918) ∨ (¬ p237)) : (¬ p918) ∨ p185 ∨ p789 ∨ (¬ p41) ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h22578 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step33302 (p185 p224 p237 p657 p918 p1385 : Prop)
    (h26887 : p657 ∨ p224)
    (h26851 : p237 ∨ p185)
    (h22352 : p1385 ∨ (¬ p918) ∨ (¬ p237) ∨ (¬ p657)) : p1385 ∨ (¬ p918) ∨ p224 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1385) := fun hu => hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h22352 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step33303 (p18 p41 p45 p576 p581 : Prop)
    (h26879 : p581 ∨ p576)
    (h26831 : p45 ∨ p41)
    (h22136 : (¬ p45) ∨ p576 ∨ (¬ p581) ∨ (¬ p18)) : p576 ∨ (¬ p18) ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h22136 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)

theorem step33305 (p41 p45 p47 : Prop)
    (h26830 : (¬ p41) ∨ (¬ p45))
    (h22129 : p45 ∨ p47) : (¬ p41) ∨ p47 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p47) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p45) := by
    rcases h26830 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h22129 with q0 | q1
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)

theorem step33309 (p63 p84 p85 : Prop)
    (h26835 : p85 ∨ p63)
    (h22278 : p84 ∨ (¬ p85)) : p84 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p84) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr hu)
  have u2 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h22278 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)

theorem step33310 (p344 p455 p897 p904 p1084 : Prop)
    (h26898 : (¬ p897) ∨ (¬ p904))
    (h22354 : p904 ∨ (¬ p1084) ∨ (¬ p455) ∨ (¬ p344)) : (¬ p344) ∨ (¬ p1084) ∨ (¬ p455) ∨ (¬ p897) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p904) := by
    rcases h26898 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h22354 with q0 | q1 | q2 | q3
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)

theorem step33311 (p161 p532 p633 p636 p1084 p1225 : Prop)
    (h26885 : p636 ∨ p633)
    (h26925 : p1225 ∨ p161)
    (h21972 : (¬ p1225) ∨ (¬ p532) ∨ (¬ p1084) ∨ (¬ p636)) : p633 ∨ p161 ∨ (¬ p532) ∨ (¬ p1084) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p161) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h21972 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step33312 (p11 p258 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h21866 : p258 ∨ (¬ p1077) ∨ (¬ p11)) : (¬ p11) ∨ p258 ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p258) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h21866 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)

theorem step33315 (p2 p15 p86 p185 p237 p419 p423 p1044 p1115 p1116 p1141 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26915 : p1116 ∨ p1115)
    (h26851 : p237 ∨ p185)
    (h22544 : p15 ∨ (¬ p1141) ∨ (¬ p86) ∨ (¬ p419) ∨ (¬ p1044) ∨ (¬ p1116) ∨ (¬ p237) ∨ (¬ p2)) : p423 ∨ p1115 ∨ (¬ p2) ∨ p15 ∨ (¬ p1044) ∨ (¬ p419) ∨ p185 ∨ (¬ p86) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1115) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h22544 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u2)

theorem step33316 (p185 p224 p237 p789 p836 p858 p980 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26896 : (¬ p789) ∨ (¬ p858))
    (h26851 : p237 ∨ p185)
    (h22508 : p858 ∨ (¬ p980) ∨ (¬ p1333) ∨ p836 ∨ (¬ p224) ∨ (¬ p237)) : p1325 ∨ (¬ p789) ∨ p185 ∨ p836 ∨ (¬ p980) ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : (¬ p858) := by
    rcases h26896 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u8 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h22508 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u8)

theorem step33317 (p17 p185 p258 p288 p583 p633 : Prop)
    (h26854 : (¬ p258) ∨ (¬ p288))
    (h21846 : (¬ p185) ∨ p17 ∨ (¬ p583) ∨ p288 ∨ (¬ p633)) : (¬ p258) ∨ (¬ p633) ∨ (¬ p583) ∨ (¬ p185) ∨ p17 := by
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
  have u2 : p583 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p288) := by
    rcases h26854 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h21846 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u1)

theorem step33321 (p1115 p1116 p1118 : Prop)
    (h26914 : (¬ p1115) ∨ (¬ p1116))
    (h23288 : p1118 ∨ p1116) : p1118 ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1118) := fun hu => hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1116) := by
    rcases h26914 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23288 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33325 (p918 p923 p928 : Prop)
    (h26900 : (¬ p918) ∨ (¬ p928))
    (h22484 : p923 ∨ p928) : p923 ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p923) := fun hu => hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p928) := by
    rcases h26900 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h22484 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33327 (p63 p836 p897 p918 p928 p1115 p1116 : Prop)
    (h26900 : (¬ p918) ∨ (¬ p928))
    (h26915 : p1116 ∨ p1115)
    (h22414 : p897 ∨ p928 ∨ (¬ p836) ∨ (¬ p63) ∨ (¬ p1116)) : (¬ p836) ∨ p897 ∨ (¬ p918) ∨ (¬ p63) ∨ p1115 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p928) := by
    rcases h26900 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u6 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h22414 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u1 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)

theorem step33328 (p17 p256 p262 : Prop)
    (h26852 : (¬ p17) ∨ (¬ p256))
    (h22142 : p262 ∨ p256) : p262 ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p262) := fun hu => hn (Or.inl hu)
  have u1 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p256) := by
    rcases h26852 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h22142 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33333 (p134 p136 p142 : Prop)
    (h26840 : (¬ p134) ∨ (¬ p142))
    (h21927 : p136 ∨ p142) : p136 ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p136) := fun hu => hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p142) := by
    rcases h26840 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h21927 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33334 (p834 p836 p840 : Prop)
    (h26894 : (¬ p836) ∨ (¬ p840))
    (h22305 : p834 ∨ p840) : p834 ∨ (¬ p836) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p834) := fun hu => hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p840) := by
    rcases h26894 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h22305 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33339 (p224 p734 p836 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h22420 : (¬ p734) ∨ p224 ∨ (¬ p836) ∨ (¬ p1116)) : (¬ p734) ∨ p1115 ∨ p224 ∨ (¬ p836) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1115) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h22420 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step33342 (p10 p24 p323 p495 p595 p596 p633 : Prop)
    (h26861 : p323 ∨ p10)
    (h22635 : p633 ∨ (¬ p323) ∨ (¬ p495) ∨ (¬ p596) ∨ (¬ p595) ∨ (¬ p24)) : p633 ∨ (¬ p495) ∨ (¬ p595) ∨ p10 ∨ (¬ p24) ∨ (¬ p596) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p596 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h22635 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u4)

theorem step33344 (p8 p10 p15 p21 p69 p101 p234 p323 p329 p350 p419 p600 p1187 p1188 p1366 : Prop)
    (h26861 : p323 ∨ p10)
    (h26921 : p1187 ∨ p234)
    (h26833 : p69 ∨ p15)
    (h22096 : (¬ p1366) ∨ (¬ p419) ∨ (¬ p1188) ∨ (¬ p1187) ∨ (¬ p350) ∨ (¬ p101) ∨ (¬ p69) ∨ (¬ p600) ∨ (¬ p323) ∨ (¬ p329) ∨ (¬ p8) ∨ (¬ p21)) : (¬ p101) ∨ (¬ p350) ∨ (¬ p600) ∨ p10 ∨ (¬ p329) ∨ (¬ p21) ∨ (¬ p1366) ∨ p234 ∨ (¬ p1188) ∨ (¬ p419) ∨ (¬ p8) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p600 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p329 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))
  have u12 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u13 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u14 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  rcases h22096 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u13)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u14)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u12)
  · exact False.elim (q9 u4)
  · exact False.elim (q10 u10)
  · exact False.elim (q11 u5)

theorem step33345 (p12 p1036 p1044 : Prop)
    (h26906 : (¬ p12) ∨ (¬ p1036))
    (h21840 : p1044 ∨ p1036) : p1044 ∨ (¬ p12) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1044) := fun hu => hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1036) := by
    rcases h26906 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h21840 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33347 (p1385 p1387 p1393 : Prop)
    (h26932 : (¬ p1385) ∨ (¬ p1393))
    (h22426 : p1387 ∨ p1393) : p1387 ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1387) := fun hu => hn (Or.inl hu)
  have u1 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1393) := by
    rcases h26932 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h22426 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33352 (p2 p476 p481 : Prop)
    (h26872 : (¬ p2) ∨ (¬ p481))
    (h22551 : p476 ∨ p481) : p476 ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p476) := fun hu => hn (Or.inl hu)
  have u1 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p481) := by
    rcases h26872 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h22551 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33353 (p312 p532 p980 p983 p1055 p1061 : Prop)
    (h26903 : p983 ∨ p980)
    (h26909 : p1061 ∨ p1055)
    (h22486 : (¬ p532) ∨ (¬ p983) ∨ p980 ∨ (¬ p312) ∨ (¬ p1061)) : p980 ∨ p1055 ∨ (¬ p312) ∨ (¬ p532) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p312 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h22486 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step33354 (p101 p121 p285 p1115 p1206 : Prop)
    (h26922 : (¬ p121) ∨ (¬ p1206))
    (h21886 : p1206 ∨ (¬ p285) ∨ (¬ p101) ∨ (¬ p1115)) : (¬ p101) ∨ (¬ p285) ∨ (¬ p1115) ∨ (¬ p121) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p285 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p1206) := by
    rcases h26922 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h21886 with q0 | q1 | q2 | q3
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)

theorem step33355 (p12 p168 p185 p237 p1115 p1116 p1346 : Prop)
    (h26914 : (¬ p1115) ∨ (¬ p1116))
    (h26851 : p237 ∨ p185)
    (h21920 : (¬ p237) ∨ (¬ p168) ∨ p1346 ∨ p1116 ∨ (¬ p12)) : (¬ p168) ∨ p1346 ∨ (¬ p1115) ∨ p185 ∨ (¬ p12) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p168 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1346) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p1116) := by
    rcases h26914 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u6 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h21920 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u0)
  · exact False.elim (u1 q2)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u4)

theorem step33356 (p12 p168 p918 p928 p1115 p1116 p1273 : Prop)
    (h26901 : p928 ∨ p918)
    (h26914 : (¬ p1115) ∨ (¬ p1116))
    (h22297 : p1273 ∨ (¬ p928) ∨ (¬ p168) ∨ p1116 ∨ (¬ p12)) : (¬ p168) ∨ (¬ p12) ∨ p1273 ∨ p918 ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p168 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1273) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : (¬ p1116) := by
    rcases h26914 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  rcases h22297 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u1)

theorem step33357 (p134 p137 p142 : Prop)
    (h26840 : (¬ p134) ∨ (¬ p142))
    (h24306 : p142 ∨ p137) : (¬ p134) ∨ p137 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p137) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p142) := by
    rcases h26840 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h24306 with q0 | q1
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)

theorem step33358 (p134 p138 p142 p148 : Prop)
    (h26840 : (¬ p134) ∨ (¬ p142))
    (h22637 : p148 ∨ p138 ∨ p142) : p148 ∨ p138 ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p148) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p138) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p142) := by
    rcases h26840 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h22637 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (u3 q2)

theorem step33360 (p11 p12 p110 p258 p288 : Prop)
    (h26855 : p288 ∨ p258)
    (h22253 : (¬ p288) ∨ (¬ p110) ∨ (¬ p12) ∨ (¬ p11)) : (¬ p11) ∨ (¬ p110) ∨ p258 ∨ (¬ p12) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h22253 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)

theorem step33361 (p12 p110 p124 p304 p961 : Prop)
    (h26858 : (¬ p124) ∨ (¬ p304))
    (h22243 : (¬ p961) ∨ p304 ∨ (¬ p110) ∨ (¬ p12)) : (¬ p961) ∨ (¬ p110) ∨ (¬ p124) ∨ (¬ p12) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p304) := by
    rcases h26858 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h22243 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)

theorem step33362 (p918 p980 p983 p1096 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h26903 : p983 ∨ p980)
    (h22511 : (¬ p983) ∨ (¬ p1096) ∨ p918 ∨ (¬ p1116)) : p1115 ∨ p980 ∨ (¬ p1096) ∨ p918 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1115) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h22511 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u3 q2)
  · exact False.elim (q3 u4)

theorem step33363 (p234 p1187 p1193 : Prop)
    (h26920 : (¬ p234) ∨ (¬ p1187))
    (h21797 : p1187 ∨ p1193) : (¬ p234) ∨ p1193 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1193) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p1187) := by
    rcases h26920 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h21797 with q0 | q1
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)

theorem step33367 (p8 p15 p49 p84 p224 p242 p419 p435 p595 p616 p657 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26883 : p616 ∨ p595)
    (h26887 : p657 ∨ p224)
    (h22368 : (¬ p435) ∨ (¬ p616) ∨ (¬ p242) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p657) ∨ (¬ p996) ∨ (¬ p15) ∨ (¬ p8)) : p419 ∨ (¬ p8) ∨ (¬ p242) ∨ p595 ∨ (¬ p435) ∨ p224 ∨ (¬ p49) ∨ (¬ p15) ∨ (¬ p84) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h22368 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u1)

theorem step33371 (p101 p102 p104 : Prop)
    (h26836 : (¬ p101) ∨ (¬ p102))
    (h21934 : p104 ∨ p102) : p104 ∨ (¬ p101) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p104) := fun hu => hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p102) := by
    rcases h26836 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h21934 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33378 (p17 p256 p261 : Prop)
    (h26852 : (¬ p17) ∨ (¬ p256))
    (h22105 : p261 ∨ p256) : p261 ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p261) := fun hu => hn (Or.inl hu)
  have u1 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p256) := by
    rcases h26852 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h22105 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33383 (p17 p63 p126 p301 p420 p601 : Prop)
    (h26857 : p301 ∨ p126)
    (h26881 : p601 ∨ p420)
    (h21929 : (¬ p17) ∨ p63 ∨ (¬ p301) ∨ (¬ p601)) : p126 ∨ p420 ∨ (¬ p17) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p420) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h21929 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step33389 (p185 p237 p238 : Prop)
    (h26850 : (¬ p185) ∨ (¬ p237))
    (h22014 : p238 ∨ p237) : p238 ∨ (¬ p185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p238) := fun hu => hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p237) := by
    rcases h26850 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h22014 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33390 (p189 p193 p1035 p1226 p1346 : Prop)
    (h26845 : p193 ∨ p189)
    (h22071 : (¬ p193) ∨ (¬ p1226) ∨ p1346 ∨ (¬ p1035)) : (¬ p1226) ∨ p1346 ∨ p189 ∨ (¬ p1035) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1346) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h22071 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)

theorem step33391 (p101 p102 p103 : Prop)
    (h26836 : (¬ p101) ∨ (¬ p102))
    (h21873 : p103 ∨ p102) : p103 ∨ (¬ p101) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p103) := fun hu => hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p102) := by
    rcases h26836 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h21873 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33395 (p12 p124 p265 p304 p1076 : Prop)
    (h26859 : p304 ∨ p124)
    (h22405 : (¬ p1076) ∨ (¬ p304) ∨ (¬ p265) ∨ (¬ p12)) : (¬ p1076) ∨ p124 ∨ (¬ p12) ∨ (¬ p265) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h22405 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)

theorem step33396 (p10 p121 p126 p301 p419 p996 p1206 p1366 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26857 : p301 ∨ p126)
    (h26904 : (¬ p419) ∨ (¬ p996))
    (h21911 : (¬ p1366) ∨ p996 ∨ (¬ p1206) ∨ (¬ p301) ∨ p10) : (¬ p1366) ∨ p121 ∨ p10 ∨ p126 ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p126) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : (¬ p996) := by
    rcases h26904 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  rcases h21911 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (u2 q4)

theorem step33400 (p10 p126 p303 p419 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h22213 : p126 ∨ (¬ p303) ∨ (¬ p996) ∨ p10) : p126 ∨ p419 ∨ (¬ p303) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h22213 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (u3 q3)

theorem step33408 (p344 p346 p349 : Prop)
    (h26862 : (¬ p344) ∨ (¬ p346))
    (h24627 : p349 ∨ p346) : p349 ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p349) := fun hu => hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p346) := by
    rcases h26862 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24627 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33412 (p8 p110 p344 p346 p557 p687 p710 p734 : Prop)
    (h26888 : (¬ p8) ∨ (¬ p710))
    (h26863 : p346 ∨ p344)
    (h22579 : (¬ p687) ∨ (¬ p734) ∨ (¬ p346) ∨ (¬ p110) ∨ p710 ∨ (¬ p557)) : (¬ p687) ∨ (¬ p110) ∨ (¬ p734) ∨ (¬ p557) ∨ (¬ p8) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p710) := by
    rcases h26888 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  have u7 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h22579 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u1)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)

theorem step33413 (p41 p89 p185 p237 p918 p928 p1074 p1115 p1116 : Prop)
    (h26851 : p237 ∨ p185)
    (h26900 : (¬ p918) ∨ (¬ p928))
    (h26915 : p1116 ∨ p1115)
    (h22419 : (¬ p1074) ∨ p928 ∨ (¬ p41) ∨ (¬ p89) ∨ (¬ p1116) ∨ (¬ p237)) : p185 ∨ (¬ p918) ∨ p1115 ∨ (¬ p41) ∨ (¬ p1074) ∨ (¬ p89) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1074 := by
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
  have u7 : (¬ p928) := by
    rcases h26900 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u8 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h22419 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u6)

theorem step33418 (p11 p1443 p1493 : Prop)
    (h26934 : (¬ p11) ∨ (¬ p1443))
    (h23344 : p1493 ∨ p1443) : p1493 ∨ (¬ p11) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1493) := fun hu => hn (Or.inl hu)
  have u1 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1443) := by
    rcases h26934 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23344 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33419 (p11 p1443 p1490 : Prop)
    (h26934 : (¬ p11) ∨ (¬ p1443))
    (h24837 : p1490 ∨ p1443) : p1490 ∨ (¬ p11) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1490) := fun hu => hn (Or.inl hu)
  have u1 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1443) := by
    rcases h26934 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24837 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33433 (p918 p922 p928 : Prop)
    (h26900 : (¬ p918) ∨ (¬ p928))
    (h23530 : p922 ∨ p928) : p922 ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p922) := fun hu => hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p928) := by
    rcases h26900 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23530 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33442 (p420 p596 p599 p601 : Prop)
    (h26880 : (¬ p420) ∨ (¬ p601))
    (h22452 : p599 ∨ p596 ∨ p601) : p599 ∨ p596 ∨ (¬ p420) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p599) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p596) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p601) := by
    rcases h26880 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h22452 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (u3 q2)

theorem step33448 (p134 p138 p142 p153 : Prop)
    (h26840 : (¬ p134) ∨ (¬ p142))
    (h22638 : p153 ∨ p138 ∨ p142) : p153 ∨ p138 ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p153) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p138) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p142) := by
    rcases h26840 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h22638 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (u3 q2)

theorem step33449 (p134 p138 p142 p152 : Prop)
    (h26840 : (¬ p134) ∨ (¬ p142))
    (h22639 : p152 ∨ p138 ∨ p142) : p152 ∨ p138 ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p152) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p138) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p142) := by
    rcases h26840 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h22639 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (u3 q2)

theorem step33450 (p134 p138 p142 p151 : Prop)
    (h26840 : (¬ p134) ∨ (¬ p142))
    (h22640 : p151 ∨ p138 ∨ p142) : p151 ∨ p138 ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p151) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p138) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p142) := by
    rcases h26840 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h22640 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (u3 q2)

theorem step33451 (p134 p138 p142 p150 : Prop)
    (h26840 : (¬ p134) ∨ (¬ p142))
    (h22641 : p150 ∨ p138 ∨ p142) : p150 ∨ p138 ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p150) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p138) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p142) := by
    rcases h26840 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h22641 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (u3 q2)

theorem step33456 (p6 p18 p19 p48 p63 p64 p85 p1096 : Prop)
    (h26835 : p85 ∨ p63)
    (h26829 : p19 ∨ p18)
    (h22865 : (¬ p1096) ∨ (¬ p6) ∨ (¬ p19) ∨ (¬ p48) ∨ (¬ p64) ∨ (¬ p85)) : (¬ p1096) ∨ (¬ p64) ∨ p63 ∨ (¬ p6) ∨ p18 ∨ (¬ p48) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h22865 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)

theorem step33457 (p18 p19 p422 p1035 p1212 p1256 p1508 : Prop)
    (h26928 : (¬ p422) ∨ (¬ p1256))
    (h26829 : p19 ∨ p18)
    (h24022 : p1508 ∨ (¬ p1212) ∨ (¬ p1035) ∨ (¬ p19) ∨ p1256) : (¬ p422) ∨ (¬ p1035) ∨ p18 ∨ p1508 ∨ (¬ p1212) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1508) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1212 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p1256) := by
    rcases h26928 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h24022 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (u5 q4)

theorem step33458 (p15 p63 p189 p193 : Prop)
    (h26844 : (¬ p189) ∨ (¬ p193))
    (h23728 : (¬ p15) ∨ p193 ∨ p63) : (¬ p15) ∨ p63 ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p193) := by
    rcases h26844 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h23728 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (u3 q1)
  · exact False.elim (u1 q2)

theorem step33461 (p15 p17 p63 p83 p85 p576 p581 : Prop)
    (h26835 : p85 ∨ p63)
    (h26879 : p581 ∨ p576)
    (h23702 : (¬ p15) ∨ (¬ p83) ∨ (¬ p581) ∨ (¬ p85) ∨ (¬ p17)) : (¬ p15) ∨ p63 ∨ (¬ p17) ∨ p576 ∨ (¬ p83) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h23702 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)

theorem step33463 (p15 p41 p47 p63 p85 p163 p918 : Prop)
    (h26835 : p85 ∨ p63)
    (h23962 : (¬ p918) ∨ p163 ∨ (¬ p47) ∨ (¬ p41) ∨ (¬ p85) ∨ (¬ p15)) : (¬ p15) ∨ p63 ∨ (¬ p47) ∨ (¬ p918) ∨ (¬ p41) ∨ p163 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h23962 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u0)

theorem step33470 (p15 p258 p495 p499 p1096 : Prop)
    (h26874 : (¬ p495) ∨ (¬ p499))
    (h24056 : p499 ∨ (¬ p1096) ∨ (¬ p15) ∨ (¬ p258)) : (¬ p495) ∨ (¬ p258) ∨ (¬ p1096) ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p499) := by
    rcases h26874 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h24056 with q0 | q1 | q2 | q3
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)

theorem step33471 (p15 p63 p124 p304 p580 p633 : Prop)
    (h26859 : p304 ∨ p124)
    (h24146 : (¬ p15) ∨ (¬ p580) ∨ (¬ p633) ∨ p63 ∨ (¬ p304)) : p124 ∨ (¬ p633) ∨ p63 ∨ (¬ p580) ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h24146 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (u2 q3)
  · exact False.elim (q4 u5)

theorem step33477 (p382 p406 p595 p1229 : Prop)
    (h26868 : (¬ p382) ∨ (¬ p406))
    (h24149 : (¬ p1229) ∨ p595 ∨ p406) : (¬ p1229) ∨ p595 ∨ (¬ p382) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p406) := by
    rcases h26868 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h24149 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (u3 q2)

theorem step33478 (p2 p63 p85 p192 p234 p1096 : Prop)
    (h26835 : p85 ∨ p63)
    (h23289 : (¬ p234) ∨ (¬ p1096) ∨ (¬ p85) ∨ (¬ p192) ∨ (¬ p2)) : (¬ p2) ∨ (¬ p1096) ∨ (¬ p192) ∨ p63 ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h23289 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)

theorem step33482 (p3 p8 p12 p38 p49 p63 p85 p226 p664 p1036 p1096 : Prop)
    (h26847 : p226 ∨ p3)
    (h26907 : p1036 ∨ p12)
    (h26835 : p85 ∨ p63)
    (h23299 : (¬ p1096) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p226) ∨ (¬ p1036) ∨ (¬ p664) ∨ (¬ p8) ∨ (¬ p85)) : p3 ∨ p12 ∨ p63 ∨ (¬ p49) ∨ (¬ p38) ∨ (¬ p1096) ∨ (¬ p8) ∨ (¬ p664) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h23299 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u10)

theorem step33483 (p17 p63 p83 p85 p576 p581 p1096 : Prop)
    (h26879 : p581 ∨ p576)
    (h26835 : p85 ∨ p63)
    (h23410 : (¬ p1096) ∨ (¬ p83) ∨ (¬ p581) ∨ (¬ p85) ∨ (¬ p17)) : (¬ p1096) ∨ p576 ∨ (¬ p17) ∨ p63 ∨ (¬ p83) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h23410 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)

theorem step33487 (p495 p499 p752 p1096 p1604 : Prop)
    (h26874 : (¬ p495) ∨ (¬ p499))
    (h23248 : p499 ∨ (¬ p1604) ∨ (¬ p1096) ∨ (¬ p752)) : (¬ p1604) ∨ (¬ p752) ∨ (¬ p495) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1604 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p752 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p499) := by
    rcases h26874 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h23248 with q0 | q1 | q2 | q3
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)

theorem step33488 (p9 p1096 p1099 : Prop)
    (h26912 : (¬ p1096) ∨ (¬ p1099))
    (h23173 : p9 ∨ p1099) : p9 ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p9) := fun hu => hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1099) := by
    rcases h26912 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23173 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33489 (p1096 p1099 p1103 : Prop)
    (h26912 : (¬ p1096) ∨ (¬ p1099))
    (h23618 : p1103 ∨ p1099) : p1103 ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1103) := fun hu => hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1099) := by
    rcases h26912 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23618 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33490 (p8 p63 p85 p344 p346 p926 p1096 p1099 : Prop)
    (h26912 : (¬ p1096) ∨ (¬ p1099))
    (h26863 : p346 ∨ p344)
    (h26835 : p85 ∨ p63)
    (h23301 : p1099 ∨ (¬ p8) ∨ (¬ p926) ∨ (¬ p85) ∨ (¬ p346)) : (¬ p1096) ∨ (¬ p8) ∨ p344 ∨ p63 ∨ (¬ p926) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p1099) := by
    rcases h26912 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u6 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h23301 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)

theorem step33497 (p2 p38 p49 p63 p85 p224 p419 p595 p657 p1287 : Prop)
    (h26887 : p657 ∨ p224)
    (h26835 : p85 ∨ p63)
    (h23249 : (¬ p657) ∨ (¬ p38) ∨ (¬ p595) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p1287) ∨ (¬ p419) ∨ (¬ p2)) : (¬ p2) ∨ (¬ p38) ∨ (¬ p1287) ∨ (¬ p595) ∨ (¬ p49) ∨ p224 ∨ p63 ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u9 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h23249 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u0)

theorem step33498 (p344 p346 p595 p642 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26863 : p346 ∨ p344)
    (h23129 : (¬ p595) ∨ (¬ p642) ∨ (¬ p1099) ∨ (¬ p346)) : p1096 ∨ p344 ∨ (¬ p642) ∨ (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1096) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p642 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h23129 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step33503 (p344 p346 p595 p664 p1076 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26863 : p346 ∨ p344)
    (h23302 : (¬ p595) ∨ (¬ p1099) ∨ (¬ p664) ∨ (¬ p1076) ∨ (¬ p346)) : p1096 ∨ p344 ∨ (¬ p1076) ∨ (¬ p595) ∨ (¬ p664) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1096) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h23302 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)

theorem step33504 (p12 p595 p664 p880 p1036 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26907 : p1036 ∨ p12)
    (h23300 : (¬ p1099) ∨ (¬ p880) ∨ (¬ p595) ∨ (¬ p1036) ∨ (¬ p664)) : (¬ p880) ∨ p1096 ∨ (¬ p595) ∨ (¬ p664) ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h23300 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)

theorem step33506 (p15 p64 p68 p69 p424 p595 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26833 : p69 ∨ p15)
    (h23377 : (¬ p595) ∨ (¬ p69) ∨ (¬ p68) ∨ (¬ p64) ∨ (¬ p796) ∨ p424) : p424 ∨ (¬ p68) ∨ (¬ p64) ∨ (¬ p595) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h23377 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (u0 q5)

theorem step33514 (p5 p15 p69 p595 p1188 : Prop)
    (h26832 : (¬ p15) ∨ (¬ p69))
    (h23632 : p5 ∨ (¬ p1188) ∨ p69 ∨ (¬ p595)) : p5 ∨ (¬ p1188) ∨ (¬ p595) ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p5) := fun hu => hn (Or.inl hu)
  have u1 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p69) := by
    rcases h26832 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h23632 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (u4 q2)
  · exact False.elim (q3 u2)

theorem step33517 (p595 p616 p1229 p1232 p1542 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h26882 : (¬ p595) ∨ (¬ p616))
    (h26281 : (¬ p1232) ∨ p616 ∨ (¬ p1542)) : (¬ p1542) ∨ p1229 ∨ (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u4 : (¬ p616) := by
    rcases h26882 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h26281 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u0)

theorem step33518 (p63 p85 p595 p616 p687 p1229 p1232 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h26835 : p85 ∨ p63)
    (h26882 : (¬ p595) ∨ (¬ p616))
    (h26282 : (¬ p1232) ∨ p616 ∨ (¬ p85) ∨ (¬ p687)) : (¬ p687) ∨ p1229 ∨ p63 ∨ (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : (¬ p616) := by
    rcases h26882 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h26282 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)

theorem step33519 (p5 p15 p68 p69 : Prop)
    (h26832 : (¬ p15) ∨ (¬ p69))
    (h23068 : p68 ∨ p69 ∨ p5) : p5 ∨ p68 ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p5) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p68) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p69) := by
    rcases h26832 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h23068 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (u0 q2)

theorem step33520 (p14 p229 p884 : Prop)
    (h26848 : (¬ p14) ∨ (¬ p229))
    (h23482 : p884 ∨ p229) : p884 ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p884) := fun hu => hn (Or.inl hu)
  have u1 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p229) := by
    rcases h26848 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23482 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33521 (p14 p15 p18 p25 p229 p495 : Prop)
    (h26848 : (¬ p14) ∨ (¬ p229))
    (h22959 : (¬ p18) ∨ p229 ∨ p25 ∨ (¬ p15) ∨ (¬ p495)) : p25 ∨ (¬ p15) ∨ (¬ p495) ∨ (¬ p14) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p25) := fun hu => hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p229) := by
    rcases h26848 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h22959 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (u5 q1)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)

theorem step33522 (p188 p189 p193 : Prop)
    (h26844 : (¬ p189) ∨ (¬ p193))
    (h23862 : p188 ∨ p193) : p188 ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p188) := fun hu => hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p193) := by
    rcases h26844 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23862 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33527 (p163 p167 p169 : Prop)
    (h26842 : (¬ p163) ∨ (¬ p167))
    (h22991 : p169 ∨ p167) : p169 ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p169) := fun hu => hn (Or.inl hu)
  have u1 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p167) := by
    rcases h26842 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h22991 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33528 (p163 p167 p170 : Prop)
    (h26842 : (¬ p163) ∨ (¬ p167))
    (h23000 : p170 ∨ p167) : p170 ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p170) := fun hu => hn (Or.inl hu)
  have u1 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p167) := by
    rcases h26842 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23000 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33529 (p15 p41 p44 p45 p63 p69 p163 p167 p918 p928 : Prop)
    (h26833 : p69 ∨ p15)
    (h26901 : p928 ∨ p918)
    (h26831 : p45 ∨ p41)
    (h26842 : (¬ p163) ∨ (¬ p167))
    (h23944 : (¬ p928) ∨ p167 ∨ (¬ p69) ∨ (¬ p44) ∨ (¬ p45) ∨ (¬ p63)) : p15 ∨ p918 ∨ (¬ p44) ∨ p41 ∨ (¬ p63) ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p15) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : (¬ p167) := by
    rcases h26842 with q0 | q1
    · exact False.elim (q0 u5)
    · exact q1
  rcases h23944 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (u9 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)

theorem step33533 (p185 p237 p243 : Prop)
    (h26851 : p237 ∨ p185)
    (h23268 : p243 ∨ (¬ p237)) : p243 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p243) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr hu)
  have u2 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h23268 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)

theorem step33536 (p11 p17 p256 p258 p288 p1080 p1349 p1443 : Prop)
    (h26934 : (¬ p11) ∨ (¬ p1443))
    (h26853 : p256 ∨ p17)
    (h26855 : p288 ∨ p258)
    (h23304 : (¬ p1349) ∨ p1443 ∨ (¬ p288) ∨ (¬ p1080) ∨ (¬ p256)) : (¬ p1349) ∨ (¬ p11) ∨ p17 ∨ (¬ p1080) ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p1443) := by
    rcases h26934 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u6 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h23304 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)

theorem step33541 (p17 p84 p185 p237 p256 p258 p286 p288 p344 p980 p1076 p1325 p1333 : Prop)
    (h26851 : p237 ∨ p185)
    (h26931 : p1333 ∨ p1325)
    (h26853 : p256 ∨ p17)
    (h26855 : p288 ∨ p258)
    (h23091 : (¬ p84) ∨ (¬ p1076) ∨ (¬ p980) ∨ (¬ p1333) ∨ (¬ p288) ∨ (¬ p286) ∨ (¬ p344) ∨ (¬ p237) ∨ (¬ p256)) : p185 ∨ p1325 ∨ (¬ p286) ∨ p17 ∨ (¬ p84) ∨ (¬ p344) ∨ p258 ∨ (¬ p980) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u12 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h23091 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u12)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u11)

theorem step33554 (p189 p193 p194 : Prop)
    (h26845 : p193 ∨ p189)
    (h24099 : p194 ∨ (¬ p193)) : p194 ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p194) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr hu)
  have u2 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h24099 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)

theorem step33557 (p17 p101 p102 p124 p138 p189 p193 p304 : Prop)
    (h26859 : p304 ∨ p124)
    (h26845 : p193 ∨ p189)
    (h26837 : p102 ∨ p101)
    (h24144 : (¬ p17) ∨ (¬ p193) ∨ (¬ p138) ∨ (¬ p102) ∨ (¬ p304)) : p124 ∨ p189 ∨ p101 ∨ (¬ p17) ∨ (¬ p138) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h24144 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u5)

theorem step33564 (p2 p6 p101 p102 : Prop)
    (h26837 : p102 ∨ p101)
    (h24223 : p6 ∨ (¬ p102) ∨ (¬ p2)) : (¬ p2) ∨ p6 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h24223 with q0 | q1 | q2
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)

theorem step33566 (p2 p124 p304 p419 : Prop)
    (h26858 : (¬ p124) ∨ (¬ p304))
    (h24120 : p304 ∨ (¬ p419) ∨ (¬ p2)) : (¬ p2) ∨ (¬ p124) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p304) := by
    rcases h26858 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24120 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)

theorem step33567 (p3 p226 p561 : Prop)
    (h26846 : (¬ p3) ∨ (¬ p226))
    (h22935 : p226 ∨ p561) : (¬ p3) ∨ p561 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p561) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p226) := by
    rcases h26846 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h22935 with q0 | q1
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)

theorem step33575 (p3 p6 p101 p121 p1080 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h23973 : (¬ p3) ∨ (¬ p1206) ∨ (¬ p6) ∨ (¬ p1080) ∨ p101) : p121 ∨ (¬ p3) ∨ (¬ p6) ∨ (¬ p1080) ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h23973 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)

theorem step33576 (p121 p134 p195 p227 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h24080 : (¬ p227) ∨ (¬ p134) ∨ (¬ p195) ∨ (¬ p1206)) : p121 ∨ (¬ p227) ∨ (¬ p195) ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h24080 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step33578 (p101 p102 p108 p121 p124 p225 p227 p309 p310 p419 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26837 : p102 ∨ p101)
    (h24021 : p225 ∨ (¬ p1206) ∨ p227 ∨ (¬ p108) ∨ (¬ p102) ∨ (¬ p309) ∨ (¬ p310) ∨ (¬ p124) ∨ (¬ p419)) : p121 ∨ p227 ∨ p101 ∨ p225 ∨ (¬ p124) ∨ (¬ p310) ∨ (¬ p108) ∨ (¬ p309) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p227) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h24021 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u9)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u8)

theorem step33585 (p2 p15 p63 p69 p224 p419 p657 p901 : Prop)
    (h26832 : (¬ p15) ∨ (¬ p69))
    (h26887 : p657 ∨ p224)
    (h24064 : p69 ∨ (¬ p901) ∨ (¬ p657) ∨ p63 ∨ (¬ p419) ∨ (¬ p2)) : (¬ p901) ∨ (¬ p2) ∨ (¬ p15) ∨ p224 ∨ (¬ p419) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p901 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p69) := by
    rcases h26832 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u7 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h24064 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u7)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u1)

theorem step33587 (p8 p63 p85 p225 p344 p495 p499 p544 p633 p710 p929 p1102 : Prop)
    (h26875 : p499 ∨ p495)
    (h26835 : p85 ∨ p63)
    (h26889 : p710 ∨ p8)
    (h26877 : p544 ∨ p225)
    (h23403 : (¬ p544) ∨ (¬ p499) ∨ (¬ p710) ∨ (¬ p929) ∨ (¬ p633) ∨ (¬ p1102) ∨ p344 ∨ (¬ p85)) : p495 ∨ (¬ p1102) ∨ p63 ∨ (¬ p929) ∨ p8 ∨ p225 ∨ p344 ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h23403 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u11)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u1)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u9)

theorem step33588 (p4 p8 p23 p108 p126 p225 p301 p309 p344 p346 p495 p499 p710 : Prop)
    (h26875 : p499 ∨ p495)
    (h26857 : p301 ∨ p126)
    (h26863 : p346 ∨ p344)
    (h26889 : p710 ∨ p8)
    (h24093 : p225 ∨ (¬ p710) ∨ (¬ p499) ∨ (¬ p23) ∨ (¬ p4) ∨ (¬ p346) ∨ (¬ p301) ∨ (¬ p108) ∨ (¬ p309)) : p495 ∨ p126 ∨ (¬ p23) ∨ (¬ p309) ∨ p344 ∨ (¬ p108) ∨ p225 ∨ (¬ p4) ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u12 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h24093 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u12)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u3)

theorem step33591 (p495 p499 p633 p1080 p1229 : Prop)
    (h26875 : p499 ∨ p495)
    (h23811 : p1229 ∨ (¬ p633) ∨ (¬ p499) ∨ (¬ p1080)) : p1229 ∨ (¬ p1080) ∨ (¬ p633) ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1229) := fun hu => hn (Or.inl hu)
  have u1 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h23811 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)

theorem step33593 (p17 p86 p126 p256 p434 p596 p1229 p1232 p1287 : Prop)
    (h26853 : p256 ∨ p17)
    (h26927 : p1232 ∨ p1229)
    (h26284 : (¬ p1232) ∨ (¬ p1287) ∨ (¬ p596) ∨ (¬ p434) ∨ (¬ p256) ∨ (¬ p86) ∨ (¬ p126)) : (¬ p434) ∨ p17 ∨ p1229 ∨ (¬ p126) ∨ (¬ p86) ∨ (¬ p1287) ∨ (¬ p596) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p596 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h26284 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u3)

theorem step33594 (p126 p301 p515 p521 : Prop)
    (h26856 : (¬ p126) ∨ (¬ p301))
    (h23651 : p521 ∨ p515 ∨ p301) : p521 ∨ p515 ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p521) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p515) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p301) := by
    rcases h26856 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h23651 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (u3 q2)

theorem step33599 (p234 p419 p595 p616 p1187 p1287 p1325 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26883 : p616 ∨ p595)
    (h23701 : (¬ p1325) ∨ (¬ p1187) ∨ (¬ p616) ∨ (¬ p1287) ∨ (¬ p419)) : p234 ∨ (¬ p419) ∨ (¬ p1287) ∨ (¬ p1325) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h23701 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u1)

theorem step33600 (p3 p8 p12 p163 p167 p224 p710 p980 p1036 p1325 : Prop)
    (h26907 : p1036 ∨ p12)
    (h26889 : p710 ∨ p8)
    (h26843 : p167 ∨ p163)
    (h23207 : (¬ p224) ∨ (¬ p710) ∨ (¬ p1036) ∨ p3 ∨ (¬ p167) ∨ (¬ p980) ∨ (¬ p1325)) : p3 ∨ p12 ∨ p8 ∨ (¬ p224) ∨ (¬ p1325) ∨ (¬ p980) ∨ p163 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h23207 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u7)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u4)

theorem step33609 (p6 p41 p45 p191 p576 p581 : Prop)
    (h26879 : p581 ∨ p576)
    (h26831 : p45 ∨ p41)
    (h23726 : (¬ p45) ∨ (¬ p191) ∨ (¬ p581) ∨ (¬ p6)) : p576 ∨ p41 ∨ (¬ p191) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h23726 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)

theorem step33620 (p2 p3 p41 p45 p192 p225 p226 p419 : Prop)
    (h26847 : p226 ∨ p3)
    (h26831 : p45 ∨ p41)
    (h23638 : (¬ p45) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p192) ∨ (¬ p419) ∨ (¬ p2)) : (¬ p2) ∨ (¬ p192) ∨ p3 ∨ (¬ p419) ∨ (¬ p225) ∨ p41 := by
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
  have u2 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h23638 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u0)

theorem step33621 (p63 p85 p88 : Prop)
    (h26834 : (¬ p63) ∨ (¬ p85))
    (h23606 : p88 ∨ p85) : p88 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p88) := fun hu => hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p85) := by
    rcases h26834 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23606 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33622 (p16 p63 p85 : Prop)
    (h26834 : (¬ p63) ∨ (¬ p85))
    (h23889 : p16 ∨ p85) : p16 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p16) := fun hu => hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p85) := by
    rcases h26834 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23889 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33623 (p420 p594 p601 : Prop)
    (h26880 : (¬ p420) ∨ (¬ p601))
    (h22899 : p594 ∨ p601) : p594 ∨ (¬ p420) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p594) := fun hu => hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p601) := by
    rcases h26880 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h22899 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33645 (p11 p12 p258 p288 p1036 p1076 : Prop)
    (h26906 : (¬ p12) ∨ (¬ p1036))
    (h26855 : p288 ∨ p258)
    (h23206 : p1036 ∨ (¬ p11) ∨ (¬ p1076) ∨ (¬ p288)) : (¬ p11) ∨ (¬ p12) ∨ (¬ p1076) ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p1036) := by
    rcases h26906 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h23206 with q0 | q1 | q2 | q3
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)

theorem step33657 (p6 p8 p225 p344 p438 p544 p687 p710 : Prop)
    (h26877 : p544 ∨ p225)
    (h26888 : (¬ p8) ∨ (¬ p710))
    (h23297 : (¬ p544) ∨ (¬ p438) ∨ (¬ p687) ∨ p710 ∨ p344 ∨ (¬ p6)) : (¬ p687) ∨ p225 ∨ (¬ p6) ∨ (¬ p438) ∨ (¬ p8) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : (¬ p710) := by
    rcases h26888 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  rcases h23297 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (u7 q3)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u2)

theorem step33660 (p2 p3 p63 p192 p224 p226 p419 p789 : Prop)
    (h26847 : p226 ∨ p3)
    (h24092 : p224 ∨ (¬ p192) ∨ p789 ∨ (¬ p226) ∨ (¬ p63) ∨ (¬ p419) ∨ (¬ p2)) : p3 ∨ p789 ∨ (¬ p63) ∨ p224 ∨ (¬ p2) ∨ (¬ p419) ∨ (¬ p192) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p789) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h24092 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u4)

theorem step33661 (p835 p836 p840 : Prop)
    (h26894 : (¬ p836) ∨ (¬ p840))
    (h22858 : p835 ∨ p840) : p835 ∨ (¬ p836) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p835) := fun hu => hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p840) := by
    rcases h26894 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h22858 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33662 (p836 p838 p840 : Prop)
    (h26894 : (¬ p836) ∨ (¬ p840))
    (h23328 : p838 ∨ p840) : p838 ∨ (¬ p836) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p838) := fun hu => hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p840) := by
    rcases h26894 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23328 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33664 (p6 p8 p14 p134 p225 p344 p346 p544 p836 p840 : Prop)
    (h26894 : (¬ p836) ∨ (¬ p840))
    (h26863 : p346 ∨ p344)
    (h26877 : p544 ∨ p225)
    (h23190 : (¬ p544) ∨ (¬ p8) ∨ (¬ p14) ∨ p840 ∨ (¬ p346) ∨ (¬ p134) ∨ (¬ p6)) : (¬ p836) ∨ (¬ p134) ∨ p344 ∨ (¬ p14) ∨ (¬ p6) ∨ p225 ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p840) := by
    rcases h26894 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u8 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h23190 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (u7 q3)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u4)

theorem step33665 (p41 p45 p163 p167 p234 p424 p918 p928 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26901 : p928 ∨ p918)
    (h26831 : p45 ∨ p41)
    (h26842 : (¬ p163) ∨ (¬ p167))
    (h23754 : (¬ p928) ∨ p167 ∨ (¬ p424) ∨ (¬ p45) ∨ (¬ p1187)) : p234 ∨ p918 ∨ p41 ∨ (¬ p424) ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : (¬ p167) := by
    rcases h26842 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  rcases h23754 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u5)

theorem step33667 (p423 p1141 p1146 : Prop)
    (h26916 : (¬ p423) ∨ (¬ p1141))
    (h23562 : p1146 ∨ p1141) : p1146 ∨ (¬ p423) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1146) := fun hu => hn (Or.inl hu)
  have u1 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1141) := by
    rcases h26916 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23562 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33685 (p228 p303 p344 p532 p728 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h25025 : (¬ p228) ∨ (¬ p303) ∨ p344 ∨ (¬ p1333) ∨ (¬ p728) ∨ (¬ p532)) : (¬ p728) ∨ p1325 ∨ (¬ p532) ∨ (¬ p303) ∨ (¬ p228) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25025 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u2)

theorem step33688 (p3 p67 p225 p226 p897 : Prop)
    (h26847 : p226 ∨ p3)
    (h23193 : p897 ∨ (¬ p226) ∨ (¬ p225) ∨ (¬ p67)) : p3 ∨ p897 ∨ (¬ p225) ∨ (¬ p67) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h23193 with q0 | q1 | q2 | q3
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)

theorem step33693 (p63 p85 p185 p224 p836 p1385 : Prop)
    (h26835 : p85 ∨ p63)
    (h23770 : (¬ p836) ∨ (¬ p185) ∨ (¬ p224) ∨ (¬ p1385) ∨ (¬ p85)) : (¬ p836) ∨ (¬ p224) ∨ (¬ p1385) ∨ p63 ∨ (¬ p185) := by
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
  have u2 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h23770 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step33694 (p424 p795 p796 : Prop)
    (h26890 : (¬ p424) ∨ (¬ p796))
    (h23781 : p795 ∨ p796) : p795 ∨ (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p795) := fun hu => hn (Or.inl hu)
  have u1 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p796) := by
    rcases h26890 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23781 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33695 (p2 p163 p167 p191 p225 p540 p836 : Prop)
    (h26842 : (¬ p163) ∨ (¬ p167))
    (h23772 : p836 ∨ (¬ p225) ∨ (¬ p540) ∨ p167 ∨ (¬ p191) ∨ (¬ p2)) : (¬ p2) ∨ (¬ p163) ∨ (¬ p191) ∨ (¬ p540) ∨ (¬ p225) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p167) := by
    rcases h26842 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23772 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u0)

theorem step33697 (p63 p160 p161 p1225 p1229 : Prop)
    (h26925 : p1225 ∨ p161)
    (h23853 : p160 ∨ (¬ p1225) ∨ p1229 ∨ (¬ p63)) : p160 ∨ p161 ∨ p1229 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p160) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p161) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h23853 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)

theorem step33703 (p15 p63 p85 p161 p185 p225 p237 p544 p980 p1035 p1225 p1325 p1333 p1508 : Prop)
    (h26877 : p544 ∨ p225)
    (h26851 : p237 ∨ p185)
    (h26925 : p1225 ∨ p161)
    (h26931 : p1333 ∨ p1325)
    (h26835 : p85 ∨ p63)
    (h23373 : (¬ p15) ∨ (¬ p980) ∨ (¬ p1333) ∨ (¬ p1225) ∨ (¬ p85) ∨ (¬ p1035) ∨ (¬ p544) ∨ (¬ p1508) ∨ (¬ p237)) : (¬ p1035) ∨ p225 ∨ p185 ∨ p161 ∨ (¬ p1508) ∨ (¬ p15) ∨ p1325 ∨ p63 ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p161) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u12 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u13 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h23373 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u12)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u13)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u10)

theorem step33713 (p138 p161 p576 p1225 p1252 p1489 : Prop)
    (h26925 : p1225 ∨ p161)
    (h22893 : (¬ p1225) ∨ (¬ p138) ∨ (¬ p576) ∨ (¬ p1252) ∨ (¬ p1489)) : (¬ p1489) ∨ p161 ∨ (¬ p138) ∨ (¬ p1252) ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p161) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1252 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h22893 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)

theorem step33721 (p1055 p1057 p1061 : Prop)
    (h26908 : (¬ p1055) ∨ (¬ p1061))
    (h23144 : p1057 ∨ p1061) : p1057 ∨ (¬ p1055) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1057) := fun hu => hn (Or.inl hu)
  have u1 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1061) := by
    rcases h26908 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23144 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33728 (p138 p234 p424 p576 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h23672 : (¬ p234) ∨ (¬ p576) ∨ (¬ p138) ∨ (¬ p796) ∨ p424) : p424 ∨ (¬ p576) ∨ (¬ p138) ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h23672 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (u0 q4)

theorem step33730 (p87 p134 p189 p234 p424 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h23722 : (¬ p796) ∨ (¬ p134) ∨ (¬ p234) ∨ (¬ p189) ∨ (¬ p87)) : p424 ∨ (¬ p189) ∨ (¬ p234) ∨ (¬ p134) ∨ (¬ p87) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h23722 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)

theorem step33733 (p50 p189 p193 p234 p790 : Prop)
    (h26845 : p193 ∨ p189)
    (h23707 : p790 ∨ (¬ p50) ∨ (¬ p234) ∨ (¬ p193)) : (¬ p50) ∨ p790 ∨ (¬ p234) ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p50 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p790) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h23707 with q0 | q1 | q2 | q3
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step33736 (p11 p264 p576 p581 p961 p1273 : Prop)
    (h26878 : (¬ p576) ∨ (¬ p581))
    (h24150 : (¬ p1273) ∨ p11 ∨ p581 ∨ (¬ p264) ∨ (¬ p961)) : (¬ p1273) ∨ (¬ p961) ∨ (¬ p264) ∨ p11 ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p264 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p581) := by
    rcases h26878 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  rcases h24150 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (u3 q1)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u1)

theorem step33739 (p897 p898 p904 : Prop)
    (h26898 : (¬ p897) ∨ (¬ p904))
    (h23167 : p898 ∨ p904) : p898 ∨ (¬ p897) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p898) := fun hu => hn (Or.inl hu)
  have u1 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p904) := by
    rcases h26898 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23167 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33740 (p1076 p1077 p1079 : Prop)
    (h26910 : (¬ p1076) ∨ (¬ p1077))
    (h22852 : p1079 ∨ p1077) : p1079 ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1079) := fun hu => hn (Or.inl hu)
  have u1 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1077) := by
    rcases h26910 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h22852 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33741 (p1076 p1077 p1081 : Prop)
    (h26910 : (¬ p1076) ∨ (¬ p1077))
    (h23439 : p1081 ∨ p1077) : p1081 ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1081) := fun hu => hn (Or.inl hu)
  have u1 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1077) := by
    rcases h26910 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23439 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33748 (p47 p87 p189 p234 p419 p790 p814 p1187 p1366 p1385 p1393 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26893 : p814 ∨ p790)
    (h26933 : p1393 ∨ p1385)
    (h23775 : (¬ p1366) ∨ (¬ p1393) ∨ (¬ p814) ∨ (¬ p47) ∨ (¬ p1187) ∨ (¬ p189) ∨ (¬ p87) ∨ (¬ p419)) : p234 ∨ (¬ p47) ∨ (¬ p189) ∨ (¬ p87) ∨ (¬ p1366) ∨ p790 ∨ (¬ p419) ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h23775 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u6)

theorem step33758 (p11 p1443 p1492 : Prop)
    (h26934 : (¬ p11) ∨ (¬ p1443))
    (h23035 : p1492 ∨ p1443) : p1492 ∨ (¬ p11) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1492) := fun hu => hn (Or.inl hu)
  have u1 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1443) := by
    rcases h26934 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23035 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33767 (p225 p539 p544 : Prop)
    (h26876 : (¬ p225) ∨ (¬ p544))
    (h23646 : p539 ∨ p544) : p539 ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p539) := fun hu => hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p544) := by
    rcases h26876 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23646 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33772 (p8 p303 p344 p710 p1055 : Prop)
    (h26889 : p710 ∨ p8)
    (h23269 : (¬ p710) ∨ p1055 ∨ p344 ∨ (¬ p303)) : p1055 ∨ p8 ∨ p344 ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1055) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p8) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h23269 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (u0 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)

theorem step33773 (p6 p8 p14 p67 p225 p344 p346 p544 p710 : Prop)
    (h26877 : p544 ∨ p225)
    (h26889 : p710 ∨ p8)
    (h26863 : p346 ∨ p344)
    (h23192 : (¬ p544) ∨ (¬ p710) ∨ (¬ p14) ∨ (¬ p346) ∨ (¬ p67) ∨ (¬ p6)) : p225 ∨ (¬ p14) ∨ (¬ p6) ∨ p8 ∨ p344 ∨ (¬ p67) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h23192 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u2)

theorem step33778 (p1055 p1056 p1061 : Prop)
    (h26908 : (¬ p1055) ∨ (¬ p1061))
    (h23150 : p1056 ∨ p1061) : p1056 ∨ (¬ p1055) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1056) := fun hu => hn (Or.inl hu)
  have u1 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1061) := by
    rcases h26908 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23150 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33779 (p110 p166 p532 p559 p1035 p1055 p1061 p1115 : Prop)
    (h26908 : (¬ p1055) ∨ (¬ p1061))
    (h23526 : (¬ p166) ∨ p1061 ∨ (¬ p1055) ∨ (¬ p532) ∨ p1115 ∨ (¬ p1035) ∨ (¬ p559) ∨ (¬ p110)) : (¬ p166) ∨ (¬ p559) ∨ (¬ p532) ∨ (¬ p1055) ∨ (¬ p1035) ∨ (¬ p110) ∨ p1115 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p166 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p559 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p1061) := by
    rcases h26908 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h23526 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u5)

theorem step33783 (p12 p110 p532 p559 p980 p983 p1055 p1061 : Prop)
    (h26903 : p983 ∨ p980)
    (h26908 : (¬ p1055) ∨ (¬ p1061))
    (h23151 : p1061 ∨ (¬ p559) ∨ (¬ p110) ∨ (¬ p12) ∨ (¬ p983) ∨ (¬ p532)) : p980 ∨ (¬ p12) ∨ (¬ p110) ∨ (¬ p559) ∨ (¬ p1055) ∨ (¬ p532) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p559 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : (¬ p1061) := by
    rcases h26908 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  rcases h23151 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)

theorem step33784 (p12 p309 p980 p983 p1036 p1056 p1076 p1226 : Prop)
    (h26906 : (¬ p12) ∨ (¬ p1036))
    (h26903 : p983 ∨ p980)
    (h23197 : p1036 ∨ (¬ p983) ∨ (¬ p1056) ∨ (¬ p1226) ∨ (¬ p1076) ∨ (¬ p309)) : (¬ p12) ∨ p980 ∨ (¬ p1226) ∨ (¬ p1056) ∨ (¬ p1076) ∨ (¬ p309) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1056 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1036) := by
    rcases h26906 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u7 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h23197 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)

theorem step33785 (p1115 p1116 p1120 : Prop)
    (h26914 : (¬ p1115) ∨ (¬ p1116))
    (h23432 : p1120 ∨ p1116) : p1120 ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1120) := fun hu => hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1116) := by
    rcases h26914 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23432 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33807 (p419 p424 p796 p1335 : Prop)
    (h26891 : p796 ∨ p424)
    (h23365 : p1335 ∨ (¬ p796) ∨ (¬ p419)) : p1335 ∨ p424 ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1335) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p424) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h23365 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)

theorem step33808 (p422 p1253 p1256 : Prop)
    (h26928 : (¬ p422) ∨ (¬ p1256))
    (h23500 : p1253 ∨ p1256) : p1253 ∨ (¬ p422) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1253) := fun hu => hn (Or.inl hu)
  have u1 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1256) := by
    rcases h26928 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23500 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33810 (p121 p1206 p1214 : Prop)
    (h26922 : (¬ p121) ∨ (¬ p1206))
    (h23488 : p1214 ∨ p1206) : p1214 ∨ (¬ p121) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1214) := fun hu => hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1206) := by
    rcases h26922 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23488 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33811 (p12 p1036 p1042 : Prop)
    (h26906 : (¬ p12) ∨ (¬ p1036))
    (h23109 : p1042 ∨ p1036) : p1042 ∨ (¬ p12) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1042) := fun hu => hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1036) := by
    rcases h26906 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23109 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33812 (p978 p980 p983 : Prop)
    (h26902 : (¬ p980) ∨ (¬ p983))
    (h23079 : p978 ∨ p983) : p978 ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p978) := fun hu => hn (Or.inl hu)
  have u1 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p983) := by
    rcases h26902 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23079 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33813 (p918 p924 p927 p928 : Prop)
    (h26900 : (¬ p918) ∨ (¬ p928))
    (h23839 : p924 ∨ p927 ∨ p928) : p924 ∨ p927 ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p924) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p927) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p928) := by
    rcases h26900 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h23839 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (u3 q2)

theorem step33816 (p8 p680 p710 : Prop)
    (h26888 : (¬ p8) ∨ (¬ p710))
    (h23161 : p680 ∨ p710) : p680 ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p680) := fun hu => hn (Or.inl hu)
  have u1 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p710) := by
    rcases h26888 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23161 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33817 (p224 p657 p663 : Prop)
    (h26886 : (¬ p224) ∨ (¬ p657))
    (h23880 : p663 ∨ p657) : p663 ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p663) := fun hu => hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p657) := by
    rcases h26886 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23880 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33820 (p23 p101 p134 p163 p167 p633 p636 : Prop)
    (h26885 : p636 ∨ p633)
    (h26842 : (¬ p163) ∨ (¬ p167))
    (h23899 : p167 ∨ (¬ p636) ∨ (¬ p134) ∨ (¬ p23) ∨ p101) : p633 ∨ (¬ p163) ∨ p101 ∨ (¬ p23) ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : (¬ p167) := by
    rcases h26842 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23899 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (u2 q4)

theorem step33822 (p576 p577 p581 : Prop)
    (h26878 : (¬ p576) ∨ (¬ p581))
    (h23688 : p577 ∨ p581) : p577 ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p577) := fun hu => hn (Or.inl hu)
  have u1 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p581) := by
    rcases h26878 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23688 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33823 (p575 p576 p581 : Prop)
    (h26878 : (¬ p576) ∨ (¬ p581))
    (h23624 : p575 ∨ p581) : p575 ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p575) := fun hu => hn (Or.inl hu)
  have u1 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p581) := by
    rcases h26878 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23624 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33824 (p533 p980 p983 : Prop)
    (h26902 : (¬ p980) ∨ (¬ p983))
    (h23049 : p533 ∨ p983) : p533 ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p533) := fun hu => hn (Or.inl hu)
  have u1 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p983) := by
    rcases h26902 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23049 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33825 (p495 p496 p499 : Prop)
    (h26874 : (¬ p495) ∨ (¬ p499))
    (h23451 : p496 ∨ p499) : p496 ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p496) := fun hu => hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p499) := by
    rcases h26874 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23451 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33826 (p158 p185 p237 : Prop)
    (h26850 : (¬ p185) ∨ (¬ p237))
    (h23556 : p158 ∨ p237) : p158 ∨ (¬ p185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p158) := fun hu => hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p237) := by
    rcases h26850 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23556 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33835 (p2 p15 p88 p188 p424 p495 p499 p577 p897 p904 p1096 : Prop)
    (h26874 : (¬ p495) ∨ (¬ p499))
    (h26899 : p904 ∨ p897)
    (h26290 : p499 ∨ (¬ p88) ∨ (¬ p424) ∨ (¬ p2) ∨ (¬ p1096) ∨ (¬ p904) ∨ (¬ p15) ∨ (¬ p577) ∨ (¬ p188)) : (¬ p2) ∨ (¬ p88) ∨ (¬ p424) ∨ (¬ p188) ∨ (¬ p495) ∨ (¬ p1096) ∨ (¬ p15) ∨ p897 ∨ (¬ p577) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p499) := by
    rcases h26874 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  have u10 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h26290 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u3)

theorem step33837 (p88 p189 p344 p422 p595 p756 p924 p1044 p1076 p1077 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26911 : p1077 ∨ p1076)
    (h23840 : p756 ∨ (¬ p924) ∨ (¬ p1077) ∨ (¬ p1044) ∨ (¬ p1099) ∨ (¬ p344) ∨ (¬ p595) ∨ (¬ p422) ∨ (¬ p189) ∨ (¬ p88)) : (¬ p422) ∨ (¬ p1044) ∨ (¬ p924) ∨ p1096 ∨ (¬ p88) ∨ (¬ p344) ∨ p1076 ∨ (¬ p595) ∨ (¬ p189) ∨ p756 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p756) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h23840 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u8)
  · exact False.elim (q9 u4)

theorem step33847 (p18 p19 p23 : Prop)
    (h26828 : (¬ p18) ∨ (¬ p19))
    (h23312 : p23 ∨ p19) : p23 ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p23) := fun hu => hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p19) := by
    rcases h26828 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23312 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33848 (p18 p19 p22 : Prop)
    (h26828 : (¬ p18) ∨ (¬ p19))
    (h23396 : p22 ∨ p19) : p22 ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p22) := fun hu => hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p19) := by
    rcases h26828 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23396 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33849 (p18 p19 p20 : Prop)
    (h26828 : (¬ p18) ∨ (¬ p19))
    (h23042 : p20 ∨ p19) : p20 ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p20) := fun hu => hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p19) := by
    rcases h26828 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h23042 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33858 (p3 p15 p69 p224 p225 p226 p234 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26847 : p226 ∨ p3)
    (h26833 : p69 ∨ p15)
    (h23705 : (¬ p225) ∨ (¬ p1187) ∨ (¬ p224) ∨ (¬ p69) ∨ (¬ p226)) : p234 ∨ p3 ∨ p15 ∨ (¬ p225) ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h23705 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)

theorem step33862 (p2 p6 p63 p126 p188 p191 p301 p303 p424 : Prop)
    (h26857 : p301 ∨ p126)
    (h24105 : p63 ∨ (¬ p191) ∨ (¬ p188) ∨ (¬ p6) ∨ (¬ p424) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p2)) : (¬ p2) ∨ p126 ∨ (¬ p191) ∨ (¬ p303) ∨ p63 ∨ (¬ p424) ∨ (¬ p188) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h24105 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u0)

theorem step33868 (p126 p258 p288 p344 : Prop)
    (h26855 : p288 ∨ p258)
    (h24053 : (¬ p344) ∨ (¬ p288) ∨ p126) : p126 ∨ (¬ p344) ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h24053 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (u0 q2)

theorem step33879 (p189 p193 p227 p228 p266 p419 p790 : Prop)
    (h26845 : p193 ∨ p189)
    (h23671 : p790 ∨ (¬ p193) ∨ (¬ p266) ∨ (¬ p228) ∨ (¬ p227) ∨ (¬ p419)) : (¬ p266) ∨ p189 ∨ (¬ p419) ∨ (¬ p227) ∨ (¬ p228) ∨ p790 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h23671 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)

theorem step33883 (p41 p63 p134 p142 p495 p499 : Prop)
    (h26874 : (¬ p495) ∨ (¬ p499))
    (h26840 : (¬ p134) ∨ (¬ p142))
    (h23966 : p499 ∨ p142 ∨ (¬ p41) ∨ (¬ p63)) : (¬ p41) ∨ (¬ p495) ∨ (¬ p63) ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
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
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p499) := by
    rcases h26874 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u5 : (¬ p142) := by
    rcases h26840 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h23966 with q0 | q1 | q2 | q3
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)

theorem step33884 (p63 p138 p165 p185 p189 p193 p237 p495 p499 : Prop)
    (h26874 : (¬ p495) ∨ (¬ p499))
    (h26845 : p193 ∨ p189)
    (h26851 : p237 ∨ p185)
    (h23597 : p499 ∨ (¬ p165) ∨ (¬ p237) ∨ (¬ p193) ∨ (¬ p63) ∨ (¬ p138)) : (¬ p165) ∨ (¬ p495) ∨ p189 ∨ (¬ p138) ∨ (¬ p63) ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p165 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p499) := by
    rcases h26874 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u7 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h23597 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step33888 (p17 p124 p256 p258 p266 p576 p581 : Prop)
    (h26878 : (¬ p576) ∨ (¬ p581))
    (h26853 : p256 ∨ p17)
    (h23399 : p581 ∨ (¬ p258) ∨ (¬ p256) ∨ (¬ p266) ∨ (¬ p124)) : (¬ p266) ∨ (¬ p258) ∨ (¬ p576) ∨ (¬ p124) ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p581) := by
    rcases h26878 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u6 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h23399 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)

theorem step33892 (p101 p102 p124 p227 p344 p664 : Prop)
    (h26837 : p102 ∨ p101)
    (h23983 : (¬ p344) ∨ (¬ p664) ∨ p227 ∨ (¬ p102) ∨ (¬ p124)) : p227 ∨ (¬ p124) ∨ (¬ p664) ∨ p101 ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p227) := fun hu => hn (Or.inl hu)
  have u1 : p124 := by
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
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h23983 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)

theorem step33896 (p224 p303 p344 p381 p532 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h23155 : p224 ∨ (¬ p1333) ∨ p344 ∨ (¬ p532) ∨ (¬ p381) ∨ (¬ p303)) : p1325 ∨ p224 ∨ (¬ p303) ∨ p344 ∨ (¬ p532) ∨ (¬ p381) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p381 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h23155 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u1 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (u3 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u2)

theorem step33897 (p11 p126 p532 p964 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h23103 : (¬ p11) ∨ (¬ p964) ∨ (¬ p1333) ∨ (¬ p532) ∨ (¬ p126)) : (¬ p532) ∨ p1325 ∨ (¬ p11) ∨ (¬ p964) ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p964 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h23103 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)

theorem step33905 (p63 p85 p160 p161 p1274 : Prop)
    (h26835 : p85 ∨ p63)
    (h23106 : (¬ p160) ∨ (¬ p161) ∨ (¬ p85) ∨ (¬ p1274)) : (¬ p160) ∨ (¬ p1274) ∨ (¬ p161) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1274 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h23106 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)

theorem step33911 (p12 p309 p559 p1035 p1036 p1055 p1056 p1076 p1226 : Prop)
    (h26906 : (¬ p12) ∨ (¬ p1036))
    (h23600 : p1036 ∨ (¬ p1226) ∨ (¬ p1035) ∨ (¬ p1056) ∨ (¬ p1055) ∨ (¬ p559) ∨ (¬ p1076) ∨ (¬ p309)) : (¬ p1035) ∨ (¬ p1226) ∨ (¬ p1055) ∨ (¬ p309) ∨ (¬ p1056) ∨ (¬ p559) ∨ (¬ p12) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1056 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p559 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p1036) := by
    rcases h26906 with q0 | q1
    · exact False.elim (q0 u6)
    · exact q1
  rcases h23600 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u3)

theorem step33913 (p15 p63 p85 p580 p1604 p1624 : Prop)
    (h26835 : p85 ∨ p63)
    (h23274 : (¬ p15) ∨ p1604 ∨ (¬ p1624) ∨ (¬ p580) ∨ (¬ p85)) : (¬ p1624) ∨ (¬ p580) ∨ p1604 ∨ (¬ p15) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1604) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h23274 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)

theorem step33919 (p15 p63 p69 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h26833 : p69 ∨ p15)
    (h24635 : (¬ p69) ∨ (¬ p1393) ∨ (¬ p63)) : p1385 ∨ p15 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1385) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h24635 with q0 | q1 | q2
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)

theorem step33921 (p6 p15 p63 p69 p101 p134 p142 : Prop)
    (h26833 : p69 ∨ p15)
    (h26841 : p142 ∨ p134)
    (h25625 : (¬ p63) ∨ (¬ p142) ∨ (¬ p69) ∨ (¬ p6) ∨ (¬ p101)) : (¬ p101) ∨ p15 ∨ (¬ p63) ∨ p134 ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25625 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)

theorem step33922 (p14 p63 p134 p142 p163 p167 : Prop)
    (h26843 : p167 ∨ p163)
    (h26841 : p142 ∨ p134)
    (h24676 : (¬ p167) ∨ (¬ p14) ∨ (¬ p142) ∨ (¬ p63)) : (¬ p14) ∨ p163 ∨ p134 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h24676 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)

theorem step33927 (p3 p6 p15 p63 p69 p101 p102 p127 p344 p687 p734 : Prop)
    (h26839 : p127 ∨ p6)
    (h26833 : p69 ∨ p15)
    (h26837 : p102 ∨ p101)
    (h25098 : (¬ p69) ∨ (¬ p63) ∨ (¬ p734) ∨ (¬ p344) ∨ (¬ p3) ∨ (¬ p127) ∨ (¬ p102) ∨ (¬ p687)) : (¬ p687) ∨ (¬ p344) ∨ (¬ p63) ∨ p6 ∨ p15 ∨ (¬ p3) ∨ (¬ p734) ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h25098 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u0)

theorem step33930 (p63 p789 p1226 p1237 p1325 p1385 p1393 p1452 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h25145 : (¬ p1452) ∨ (¬ p1226) ∨ (¬ p1393) ∨ (¬ p789) ∨ (¬ p1237) ∨ (¬ p1325) ∨ (¬ p63)) : (¬ p1452) ∨ p1385 ∨ (¬ p1325) ∨ (¬ p63) ∨ (¬ p1237) ∨ (¬ p789) ∨ (¬ p1226) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25145 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step33935 (p3 p10 p12 p17 p63 p85 p101 p124 p125 p126 p134 p142 p169 p185 p191 p226 p301 p303 p323 p364 p405 p422 p424 p595 p836 p1229 p1256 p1286 : Prop)
    (h26847 : p226 ∨ p3)
    (h26929 : p1256 ∨ p422)
    (h26834 : (¬ p63) ∨ (¬ p85))
    (h26841 : p142 ∨ p134)
    (h26860 : (¬ p10) ∨ (¬ p323))
    (h26857 : p301 ∨ p126)
    (h25638 : (¬ p595) ∨ (¬ p1286) ∨ (¬ p1229) ∨ p12 ∨ (¬ p405) ∨ (¬ p1256) ∨ p303 ∨ (¬ p364) ∨ (¬ p124) ∨ (¬ p17) ∨ (¬ p125) ∨ (¬ p185) ∨ (¬ p191) ∨ (¬ p226) ∨ p85 ∨ (¬ p836) ∨ (¬ p424) ∨ (¬ p142) ∨ (¬ p301) ∨ p323 ∨ p101 ∨ (¬ p169)) : p3 ∨ (¬ p836) ∨ (¬ p364) ∨ p12 ∨ p422 ∨ (¬ p424) ∨ p101 ∨ (¬ p405) ∨ p303 ∨ (¬ p1286) ∨ (¬ p124) ∨ (¬ p595) ∨ (¬ p1229) ∨ (¬ p17) ∨ (¬ p63) ∨ (¬ p191) ∨ (¬ p185) ∨ (¬ p125) ∨ p134 ∨ (¬ p10) ∨ p126 ∨ (¬ p169) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p405 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))
  have u15 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))
  have u16 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))
  have u17 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))
  have u18 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))))
  have u19 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))))
  have u20 : (¬ p126) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))))))
  have u21 : p169 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))))))))))))
  have u22 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u23 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u24 : (¬ p85) := by
    rcases h26834 with q0 | q1
    · exact False.elim (q0 u14)
    · exact q1
  have u25 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u18 q1)
  have u26 : (¬ p323) := by
    rcases h26860 with q0 | q1
    · exact False.elim (q0 u19)
    · exact q1
  have u27 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u20 q1)
  rcases h25638 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14 | q15 | q16 | q17 | q18 | q19 | q20 | q21
  · exact False.elim (q0 u11)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u12)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u23)
  · exact False.elim (u8 q6)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u13)
  · exact False.elim (q10 u17)
  · exact False.elim (q11 u16)
  · exact False.elim (q12 u15)
  · exact False.elim (q13 u22)
  · exact False.elim (u24 q14)
  · exact False.elim (q15 u1)
  · exact False.elim (q16 u5)
  · exact False.elim (q17 u25)
  · exact False.elim (q18 u27)
  · exact False.elim (u26 q19)
  · exact False.elim (u6 q20)
  · exact False.elim (q21 u21)

theorem step33936 (p3 p12 p39 p226 p424 p595 p796 p940 p985 p1036 p1286 p1325 p1333 : Prop)
    (h26847 : p226 ∨ p3)
    (h26931 : p1333 ∨ p1325)
    (h26891 : p796 ∨ p424)
    (h26907 : p1036 ∨ p12)
    (h25173 : (¬ p226) ∨ (¬ p39) ∨ (¬ p796) ∨ (¬ p1036) ∨ (¬ p940) ∨ (¬ p1286) ∨ (¬ p595) ∨ (¬ p985) ∨ (¬ p1333)) : (¬ p940) ∨ p3 ∨ p1325 ∨ (¬ p985) ∨ (¬ p39) ∨ p424 ∨ (¬ p1286) ∨ (¬ p595) ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p424) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u12 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h25173 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u12)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u3)
  · exact False.elim (q8 u10)

theorem step33937 (p3 p4 p5 p10 p16 p108 p124 p125 p161 p185 p226 p595 p836 p985 p1225 p1229 p1286 p1325 : Prop)
    (h26925 : p1225 ∨ p161)
    (h26847 : p226 ∨ p3)
    (h25633 : p1325 ∨ (¬ p1225) ∨ (¬ p985) ∨ (¬ p5) ∨ (¬ p595) ∨ (¬ p1286) ∨ (¬ p124) ∨ (¬ p108) ∨ (¬ p836) ∨ (¬ p10) ∨ (¬ p185) ∨ (¬ p4) ∨ (¬ p1229) ∨ (¬ p125) ∨ (¬ p226) ∨ (¬ p16)) : (¬ p1286) ∨ (¬ p125) ∨ (¬ p16) ∨ (¬ p185) ∨ (¬ p595) ∨ (¬ p1229) ∨ p1325 ∨ (¬ p985) ∨ (¬ p124) ∨ (¬ p5) ∨ (¬ p108) ∨ (¬ p4) ∨ p161 ∨ (¬ p836) ∨ p3 ∨ (¬ p10) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : (¬ p161) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))
  have u15 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))))))
  have u16 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u12 q1)
  have u17 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u14 q1)
  rcases h25633 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14 | q15
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u16)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u13)
  · exact False.elim (q9 u15)
  · exact False.elim (q10 u3)
  · exact False.elim (q11 u11)
  · exact False.elim (q12 u5)
  · exact False.elim (q13 u1)
  · exact False.elim (q14 u17)
  · exact False.elim (q15 u2)

theorem step33938 (p3 p5 p12 p226 p595 p980 p1286 p1465 : Prop)
    (h26847 : p226 ∨ p3)
    (h25635 : (¬ p1465) ∨ p980 ∨ (¬ p5) ∨ (¬ p595) ∨ (¬ p1286) ∨ p12 ∨ (¬ p226)) : p3 ∨ p980 ∨ (¬ p5) ∨ (¬ p1286) ∨ (¬ p595) ∨ (¬ p1465) ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h25635 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u7)

theorem step33939 (p224 p344 p382 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h25072 : (¬ p657) ∨ (¬ p344) ∨ (¬ p382)) : (¬ p344) ∨ p224 ∨ (¬ p382) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
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
  rcases h25072 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)

theorem step33944 (p2 p18 p19 p224 p419 p423 p657 p1141 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26829 : p19 ∨ p18)
    (h26887 : p657 ∨ p224)
    (h25532 : (¬ p657) ∨ (¬ p19) ∨ p2 ∨ (¬ p419) ∨ (¬ p1141)) : p423 ∨ p18 ∨ p224 ∨ (¬ p419) ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25532 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (u4 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step33948 (p3 p6 p127 p633 : Prop)
    (h26839 : p127 ∨ p6)
    (h25227 : (¬ p127) ∨ p3 ∨ (¬ p633)) : p3 ∨ p6 ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25227 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u2)

theorem step33950 (p3 p6 p101 p102 p108 p191 p226 p344 p346 p382 p406 p424 p1287 : Prop)
    (h26869 : p406 ∨ p382)
    (h26847 : p226 ∨ p3)
    (h26837 : p102 ∨ p101)
    (h26863 : p346 ∨ p344)
    (h25653 : (¬ p102) ∨ (¬ p1287) ∨ (¬ p424) ∨ (¬ p108) ∨ (¬ p226) ∨ (¬ p346) ∨ (¬ p406) ∨ (¬ p191) ∨ (¬ p6)) : p382 ∨ p3 ∨ (¬ p1287) ∨ (¬ p6) ∨ (¬ p191) ∨ p101 ∨ (¬ p424) ∨ (¬ p108) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u12 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h25653 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u11)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u3)

theorem step33951 (p10 p18 p19 p101 p102 p234 p323 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26860 : (¬ p10) ∨ (¬ p323))
    (h26837 : p102 ∨ p101)
    (h26829 : p19 ∨ p18)
    (h24235 : (¬ p1187) ∨ p323 ∨ (¬ p19) ∨ (¬ p102)) : p234 ∨ (¬ p10) ∨ p101 ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : (¬ p323) := by
    rcases h26860 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h24235 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)

theorem step33952 (p14 p101 p102 p633 : Prop)
    (h26837 : p102 ∨ p101)
    (h25766 : p633 ∨ (¬ p14) ∨ (¬ p102)) : p633 ∨ p101 ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25766 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step33953 (p189 p193 p382 p789 : Prop)
    (h26845 : p193 ∨ p189)
    (h25697 : (¬ p382) ∨ (¬ p789) ∨ (¬ p193)) : (¬ p382) ∨ (¬ p789) ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25697 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step33954 (p8 p224 p657 p728 p1055 : Prop)
    (h26886 : (¬ p224) ∨ (¬ p657))
    (h25073 : (¬ p728) ∨ (¬ p8) ∨ (¬ p1055) ∨ p657) : (¬ p1055) ∨ (¬ p728) ∨ (¬ p224) ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p657) := by
    rcases h26886 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h25073 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (u4 q3)

theorem step33955 (p1140 p1159 p1167 : Prop)
    (h26918 : (¬ p1140) ∨ (¬ p1159))
    (h25744 : p1167 ∨ p1159) : p1167 ∨ (¬ p1140) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1167) := fun hu => hn (Or.inl hu)
  have u1 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1159) := by
    rcases h26918 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h25744 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33961 (p12 p14 p15 p41 p45 p63 p124 p224 p304 p351 p662 p665 p836 p840 p918 p928 p1465 : Prop)
    (h26859 : p304 ∨ p124)
    (h26901 : p928 ∨ p918)
    (h26895 : p840 ∨ p836)
    (h26831 : p45 ∨ p41)
    (h25559 : (¬ p928) ∨ (¬ p1465) ∨ (¬ p665) ∨ (¬ p662) ∨ (¬ p224) ∨ (¬ p15) ∨ (¬ p45) ∨ (¬ p351) ∨ p836 ∨ (¬ p840) ∨ (¬ p14) ∨ (¬ p12) ∨ (¬ p304) ∨ (¬ p63)) : p124 ∨ (¬ p14) ∨ p918 ∨ (¬ p12) ∨ (¬ p665) ∨ (¬ p224) ∨ (¬ p662) ∨ (¬ p1465) ∨ p836 ∨ (¬ p63) ∨ (¬ p351) ∨ p41 ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p662 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))
  have u13 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u14 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u15 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u16 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  rcases h25559 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13
  · exact False.elim (q0 u14)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u16)
  · exact False.elim (q7 u10)
  · exact False.elim (u8 q8)
  · exact False.elim (q9 u15)
  · exact False.elim (q10 u1)
  · exact False.elim (q11 u3)
  · exact False.elim (q12 u13)
  · exact False.elim (q13 u9)

theorem step33969 (p17 p63 p85 p124 p304 p633 : Prop)
    (h26859 : p304 ∨ p124)
    (h26834 : (¬ p63) ∨ (¬ p85))
    (h25214 : p85 ∨ (¬ p17) ∨ (¬ p633) ∨ (¬ p304)) : p124 ∨ (¬ p633) ∨ (¬ p63) ∨ (¬ p17) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : (¬ p85) := by
    rcases h26834 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h25214 with q0 | q1 | q2 | q3
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step33972 (p63 p85 p420 p574 p601 p1385 : Prop)
    (h26881 : p601 ∨ p420)
    (h26834 : (¬ p63) ∨ (¬ p85))
    (h24874 : p574 ∨ (¬ p1385) ∨ p85 ∨ (¬ p601)) : p574 ∨ (¬ p1385) ∨ p420 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p574) := fun hu => hn (Or.inl hu)
  have u1 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : (¬ p85) := by
    rcases h26834 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h24874 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u4)

theorem step33973 (p185 p237 p239 : Prop)
    (h26850 : (¬ p185) ∨ (¬ p237))
    (h25464 : p239 ∨ p237) : p239 ∨ (¬ p185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p239) := fun hu => hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p237) := by
    rcases h26850 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h25464 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33974 (p6 p16 p18 p21 p72 p127 p134 p142 p224 p309 p310 p344 p495 p499 p621 p633 p756 p1226 p1237 : Prop)
    (h26839 : p127 ∨ p6)
    (h26841 : p142 ∨ p134)
    (h26875 : p499 ∨ p495)
    (h25748 : (¬ p344) ∨ (¬ p224) ∨ (¬ p16) ∨ (¬ p1237) ∨ (¬ p142) ∨ (¬ p1226) ∨ (¬ p309) ∨ (¬ p310) ∨ (¬ p633) ∨ p756 ∨ (¬ p499) ∨ (¬ p72) ∨ (¬ p621) ∨ (¬ p21) ∨ (¬ p18) ∨ (¬ p127)) : (¬ p1226) ∨ (¬ p1237) ∨ (¬ p21) ∨ (¬ p18) ∨ p6 ∨ (¬ p16) ∨ (¬ p344) ∨ (¬ p224) ∨ p134 ∨ (¬ p310) ∨ (¬ p309) ∨ (¬ p72) ∨ (¬ p633) ∨ p756 ∨ p495 ∨ (¬ p621) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : (¬ p756) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))
  have u15 : p621 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))))))
  have u16 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u17 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u18 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u14 q1)
  rcases h25748 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14 | q15
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u17)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u12)
  · exact False.elim (u13 q9)
  · exact False.elim (q10 u18)
  · exact False.elim (q11 u11)
  · exact False.elim (q12 u15)
  · exact False.elim (q13 u2)
  · exact False.elim (q14 u3)
  · exact False.elim (q15 u16)

theorem step33976 (p10 p101 p102 p207 p303 p323 p382 p406 : Prop)
    (h26869 : p406 ∨ p382)
    (h26836 : (¬ p101) ∨ (¬ p102))
    (h26861 : p323 ∨ p10)
    (h25737 : p102 ∨ (¬ p303) ∨ (¬ p323) ∨ (¬ p406) ∨ (¬ p207)) : p382 ∨ (¬ p101) ∨ p10 ∨ (¬ p303) ∨ (¬ p207) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : (¬ p102) := by
    rcases h26836 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u7 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25737 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)

theorem step33978 (p10 p101 p124 p323 p348 p940 : Prop)
    (h26861 : p323 ∨ p10)
    (h25187 : (¬ p940) ∨ (¬ p124) ∨ (¬ p323) ∨ (¬ p101) ∨ (¬ p348)) : (¬ p101) ∨ (¬ p124) ∨ (¬ p940) ∨ p10 ∨ (¬ p348) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25187 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)

theorem step33979 (p10 p101 p143 p262 p309 p310 p323 p633 p636 p664 p897 p904 p1076 : Prop)
    (h26899 : p904 ∨ p897)
    (h26884 : (¬ p633) ∨ (¬ p636))
    (h26861 : p323 ∨ p10)
    (h25597 : (¬ p101) ∨ (¬ p143) ∨ (¬ p1076) ∨ (¬ p664) ∨ (¬ p904) ∨ (¬ p323) ∨ (¬ p309) ∨ (¬ p310) ∨ p636 ∨ (¬ p262)) : (¬ p101) ∨ (¬ p310) ∨ (¬ p262) ∨ p897 ∨ (¬ p664) ∨ (¬ p633) ∨ (¬ p309) ∨ (¬ p1076) ∨ p10 ∨ (¬ p143) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : (¬ p636) := by
    rcases h26884 with q0 | q1
    · exact False.elim (q0 u5)
    · exact q1
  have u12 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h25597 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u1)
  · exact False.elim (u11 q8)
  · exact False.elim (q9 u2)

theorem step33981 (p10 p12 p323 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26861 : p323 ∨ p10)
    (h24806 : p12 ∨ (¬ p1077) ∨ (¬ p323)) : p12 ∨ p1076 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p12) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u4 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h24806 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)

theorem step33982 (p10 p18 p19 p101 p102 p303 p323 p344 p387 : Prop)
    (h26867 : p387 ∨ p303)
    (h26829 : p19 ∨ p18)
    (h26861 : p323 ∨ p10)
    (h26837 : p102 ∨ p101)
    (h24242 : (¬ p19) ∨ (¬ p387) ∨ (¬ p323) ∨ (¬ p344) ∨ (¬ p102)) : p303 ∨ (¬ p344) ∨ p18 ∨ p10 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h24242 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u8)

theorem step33983 (p2 p3 p226 p344 p481 : Prop)
    (h26847 : p226 ∨ p3)
    (h26873 : p481 ∨ p2)
    (h25755 : (¬ p226) ∨ (¬ p481) ∨ p344) : p3 ∨ p344 ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p2) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25755 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)

theorem step33984 (p3 p226 p560 : Prop)
    (h26846 : (¬ p3) ∨ (¬ p226))
    (h24442 : p560 ∨ p226) : p560 ∨ (¬ p3) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p560) := fun hu => hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p226) := by
    rcases h26846 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24442 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33985 (p3 p226 p563 : Prop)
    (h26846 : (¬ p3) ∨ (¬ p226))
    (h24684 : p563 ∨ p226) : p563 ∨ (¬ p3) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p563) := fun hu => hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p226) := by
    rcases h26846 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24684 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step33987 (p8 p224 p710 p789 : Prop)
    (h26889 : p710 ∨ p8)
    (h25752 : (¬ p710) ∨ (¬ p789) ∨ (¬ p224)) : (¬ p789) ∨ (¬ p224) ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25752 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)

theorem step33989 (p224 p225 p303 p344 p345 p346 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h26863 : p346 ∨ p344)
    (h24521 : p225 ∨ (¬ p657) ∨ (¬ p346) ∨ (¬ p345) ∨ (¬ p303)) : p225 ∨ p224 ∨ (¬ p345) ∨ (¬ p303) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h24521 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)

theorem step33990 (p125 p126 p264 p301 p303 p789 p858 : Prop)
    (h26856 : (¬ p126) ∨ (¬ p301))
    (h26896 : (¬ p789) ∨ (¬ p858))
    (h24730 : p858 ∨ (¬ p303) ∨ (¬ p264) ∨ (¬ p125) ∨ p301) : (¬ p125) ∨ (¬ p264) ∨ (¬ p126) ∨ (¬ p789) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p264 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p301) := by
    rcases h26856 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  have u6 : (¬ p858) := by
    rcases h26896 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h24730 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)
  · exact False.elim (u5 q4)

theorem step33991 (p224 p303 p657 p897 : Prop)
    (h26887 : p657 ∨ p224)
    (h25260 : p897 ∨ (¬ p657) ∨ (¬ p303)) : p897 ∨ p224 ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p897) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25260 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)

theorem step33992 (p12 p14 p225 p229 p303 p434 p663 p664 p1036 : Prop)
    (h26849 : p229 ∨ p14)
    (h26907 : p1036 ∨ p12)
    (h25475 : (¬ p1036) ∨ (¬ p229) ∨ (¬ p663) ∨ (¬ p664) ∨ (¬ p303) ∨ p225 ∨ (¬ p434)) : (¬ p434) ∨ (¬ p663) ∨ p225 ∨ (¬ p664) ∨ p14 ∨ (¬ p303) ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p663 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u8 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h25475 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (u2 q5)
  · exact False.elim (q6 u0)

theorem step33993 (p8 p224 p303 p657 p918 p928 : Prop)
    (h26901 : p928 ∨ p918)
    (h26887 : p657 ∨ p224)
    (h25261 : (¬ p8) ∨ (¬ p657) ∨ (¬ p928) ∨ (¬ p303)) : (¬ p8) ∨ p918 ∨ p224 ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25261 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)

theorem step33998 (p10 p101 p124 p303 p323 p387 : Prop)
    (h26867 : p387 ∨ p303)
    (h26861 : p323 ∨ p10)
    (h25205 : (¬ p387) ∨ (¬ p323) ∨ (¬ p124) ∨ (¬ p101)) : p303 ∨ (¬ p101) ∨ p10 ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25205 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)

theorem step33999 (p1 p2 p3 p124 p125 p134 p142 p191 p207 p225 p226 p362 p424 p544 p1076 : Prop)
    (h26877 : p544 ∨ p225)
    (h26841 : p142 ∨ p134)
    (h26847 : p226 ∨ p3)
    (h26865 : p362 ∨ p125)
    (h25664 : (¬ p124) ∨ (¬ p1076) ∨ (¬ p544) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p226) ∨ (¬ p424) ∨ (¬ p362) ∨ (¬ p207) ∨ (¬ p142) ∨ (¬ p191)) : (¬ p2) ∨ p225 ∨ p134 ∨ (¬ p207) ∨ (¬ p191) ∨ (¬ p1) ∨ p3 ∨ (¬ p1076) ∨ (¬ p124) ∨ p125 ∨ (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u12 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u13 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u14 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h25664 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u13)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u14)
  · exact False.elim (q8 u3)
  · exact False.elim (q9 u12)
  · exact False.elim (q10 u4)

theorem step34002 (p14 p229 p883 : Prop)
    (h26848 : (¬ p14) ∨ (¬ p229))
    (h25503 : p883 ∨ p229) : p883 ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p883) := fun hu => hn (Or.inl hu)
  have u1 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p229) := by
    rcases h26848 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h25503 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34003 (p3 p14 p15 p69 p225 p229 p344 p346 p544 p595 p664 : Prop)
    (h26848 : (¬ p14) ∨ (¬ p229))
    (h26877 : p544 ∨ p225)
    (h26863 : p346 ∨ p344)
    (h26833 : p69 ∨ p15)
    (h24700 : (¬ p346) ∨ (¬ p595) ∨ (¬ p664) ∨ (¬ p544) ∨ p229 ∨ (¬ p3) ∨ (¬ p69)) : (¬ p14) ∨ p225 ∨ p344 ∨ (¬ p3) ∨ (¬ p664) ∨ p15 ∨ (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p229) := by
    rcases h26848 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u8 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h24700 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u8)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u10)

theorem step34004 (p187 p189 p193 : Prop)
    (h26844 : (¬ p189) ∨ (¬ p193))
    (h24369 : p187 ∨ p193) : p187 ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p187) := fun hu => hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p193) := by
    rcases h26844 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24369 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34006 (p41 p121 p134 p142 p189 p193 p243 p303 p344 p926 : Prop)
    (h26845 : p193 ∨ p189)
    (h26841 : p142 ∨ p134)
    (h25297 : (¬ p121) ∨ (¬ p243) ∨ (¬ p142) ∨ p344 ∨ (¬ p303) ∨ (¬ p41) ∨ (¬ p193) ∨ (¬ p926)) : (¬ p121) ∨ (¬ p243) ∨ (¬ p41) ∨ (¬ p303) ∨ p189 ∨ p134 ∨ p344 ∨ (¬ p926) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p243 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h25297 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u9)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u7)

theorem step34007 (p3 p6 p18 p101 p102 p125 p134 p142 p191 p224 p226 p362 p657 p1076 p1077 : Prop)
    (h26847 : p226 ∨ p3)
    (h26836 : (¬ p101) ∨ (¬ p102))
    (h26841 : p142 ∨ p134)
    (h26865 : p362 ∨ p125)
    (h26911 : p1077 ∨ p1076)
    (h26886 : (¬ p224) ∨ (¬ p657))
    (h25734 : p102 ∨ p18 ∨ (¬ p142) ∨ (¬ p362) ∨ (¬ p191) ∨ (¬ p1077) ∨ (¬ p226) ∨ p657 ∨ (¬ p6)) : p3 ∨ (¬ p101) ∨ p18 ∨ p134 ∨ p125 ∨ p1076 ∨ (¬ p6) ∨ (¬ p191) ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : (¬ p102) := by
    rcases h26836 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  have u11 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u12 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u13 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u14 : (¬ p657) := by
    rcases h26886 with q0 | q1
    · exact False.elim (q0 u8)
    · exact q1
  rcases h25734 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u10 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u12)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u13)
  · exact False.elim (q6 u9)
  · exact False.elim (u14 q7)
  · exact False.elim (q8 u6)

theorem step34008 (p134 p142 p189 p193 p326 p790 : Prop)
    (h26845 : p193 ∨ p189)
    (h26841 : p142 ∨ p134)
    (h24990 : p790 ∨ (¬ p193) ∨ (¬ p326) ∨ (¬ p142)) : p790 ∨ p189 ∨ p134 ∨ (¬ p326) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h24990 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)

theorem step34009 (p18 p19 p21 : Prop)
    (h26828 : (¬ p18) ∨ (¬ p19))
    (h24479 : p21 ∨ p19) : p21 ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p21) := fun hu => hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p19) := by
    rcases h26828 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24479 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34011 (p10 p17 p140 p256 p420 p515 p601 p790 p814 : Prop)
    (h26893 : p814 ∨ p790)
    (h26881 : p601 ∨ p420)
    (h26853 : p256 ∨ p17)
    (h24882 : (¬ p601) ∨ (¬ p814) ∨ (¬ p140) ∨ (¬ p256) ∨ (¬ p515) ∨ (¬ p10)) : (¬ p515) ∨ p790 ∨ (¬ p140) ∨ p420 ∨ p17 ∨ (¬ p10) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p515 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p790) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h24882 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u5)

theorem step34013 (p344 p346 p348 : Prop)
    (h26862 : (¬ p344) ∨ (¬ p346))
    (h24340 : p348 ∨ p346) : p348 ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p348) := fun hu => hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p346) := by
    rcases h26862 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24340 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34021 (p6 p12 p134 p142 p1036 p1076 p1077 p1115 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26841 : p142 ∨ p134)
    (h26906 : (¬ p12) ∨ (¬ p1036))
    (h24868 : (¬ p1115) ∨ (¬ p142) ∨ (¬ p1077) ∨ (¬ p6) ∨ p1036) : (¬ p1115) ∨ p1076 ∨ p134 ∨ (¬ p12) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : (¬ p1036) := by
    rcases h26906 with q0 | q1
    · exact False.elim (q0 u3)
    · exact q1
  rcases h24868 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (u7 q4)

theorem step34022 (p14 p15 p16 p90 p225 p544 p664 p918 p1055 p1061 p1115 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26877 : p544 ∨ p225)
    (h26586 : p90)
    (h25570 : (¬ p1115) ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p90) ∨ (¬ p16) ∨ (¬ p1061) ∨ (¬ p664) ∨ (¬ p544) ∨ (¬ p918)) : p1055 ∨ (¬ p1115) ∨ (¬ p14) ∨ (¬ p918) ∨ p225 ∨ (¬ p16) ∨ (¬ p15) ∨ (¬ p664) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1055) := fun hu => hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p90 := by
    exact h26586
  rcases h25570 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u3)

theorem step34025 (p1115 p1116 p1117 : Prop)
    (h26914 : (¬ p1115) ∨ (¬ p1116))
    (h24560 : p1117 ∨ p1116) : p1117 ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1117) := fun hu => hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1116) := by
    rcases h26914 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24560 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34026 (p3 p12 p195 p1115 p1116 : Prop)
    (h26914 : (¬ p1115) ∨ (¬ p1116))
    (h24691 : p1116 ∨ (¬ p12) ∨ (¬ p195) ∨ (¬ p3)) : (¬ p12) ∨ (¬ p1115) ∨ (¬ p195) ∨ (¬ p3) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p1116) := by
    rcases h26914 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24691 with q0 | q1 | q2 | q3
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)

theorem step34027 (p12 p105 p134 p142 p557 p1055 p1061 p1115 p1116 : Prop)
    (h26914 : (¬ p1115) ∨ (¬ p1116))
    (h26909 : p1061 ∨ p1055)
    (h26841 : p142 ∨ p134)
    (h24397 : p1116 ∨ (¬ p1061) ∨ (¬ p12) ∨ (¬ p142) ∨ (¬ p105) ∨ (¬ p557)) : (¬ p1115) ∨ (¬ p12) ∨ (¬ p105) ∨ p1055 ∨ (¬ p557) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1116) := by
    rcases h26914 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u7 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h24397 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u4)

theorem step34029 (p2 p6 p10 p11 p17 p41 p107 p127 p134 p135 p140 p163 p167 p189 p256 p419 p424 p481 p996 p1325 p1443 : Prop)
    (h26905 : p996 ∨ p419)
    (h26935 : p1443 ∨ p11)
    (h26853 : p256 ∨ p17)
    (h26842 : (¬ p163) ∨ (¬ p167))
    (h26839 : p127 ∨ p6)
    (h26873 : p481 ∨ p2)
    (h24974 : (¬ p1443) ∨ p41 ∨ (¬ p424) ∨ (¬ p481) ∨ p167 ∨ (¬ p163) ∨ (¬ p107) ∨ (¬ p996) ∨ (¬ p10) ∨ p1325 ∨ (¬ p135) ∨ (¬ p140) ∨ p134 ∨ (¬ p189) ∨ (¬ p127) ∨ (¬ p256)) : p419 ∨ p1325 ∨ (¬ p107) ∨ p11 ∨ p17 ∨ (¬ p163) ∨ p6 ∨ p41 ∨ (¬ p424) ∨ (¬ p189) ∨ p2 ∨ p134 ∨ (¬ p140) ∨ (¬ p10) ∨ (¬ p135) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))))
  have u15 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u16 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u17 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u18 : (¬ p167) := by
    rcases h26842 with q0 | q1
    · exact False.elim (q0 u5)
    · exact q1
  have u19 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u20 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  rcases h24974 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14 | q15
  · exact False.elim (q0 u16)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u20)
  · exact False.elim (u18 q4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u15)
  · exact False.elim (q8 u13)
  · exact False.elim (u1 q9)
  · exact False.elim (q10 u14)
  · exact False.elim (q11 u12)
  · exact False.elim (u11 q12)
  · exact False.elim (q13 u9)
  · exact False.elim (q14 u19)
  · exact False.elim (q15 u17)

theorem step34030 (p41 p63 p121 p495 p499 : Prop)
    (h26874 : (¬ p495) ∨ (¬ p499))
    (h24625 : (¬ p41) ∨ p499 ∨ (¬ p63) ∨ (¬ p121)) : (¬ p41) ∨ (¬ p495) ∨ (¬ p121) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p499) := by
    rcases h26874 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24625 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)

theorem step34031 (p101 p495 p499 p1096 : Prop)
    (h26874 : (¬ p495) ∨ (¬ p499))
    (h26300 : (¬ p101) ∨ p499 ∨ (¬ p1096)) : (¬ p101) ∨ (¬ p495) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p499) := by
    rcases h26874 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h26300 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u2)

theorem step34032 (p420 p495 p499 p1096 : Prop)
    (h26874 : (¬ p495) ∨ (¬ p499))
    (h24234 : (¬ p1096) ∨ (¬ p420) ∨ p499) : (¬ p1096) ∨ (¬ p420) ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p499) := by
    rcases h26874 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h24234 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u3 q2)

theorem step34033 (p303 p384 p387 : Prop)
    (h26866 : (¬ p303) ∨ (¬ p387))
    (h24334 : p384 ∨ p387) : p384 ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p384) := fun hu => hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p387) := by
    rcases h26866 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h24334 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step34034 (p10 p303 p387 p419 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26866 : (¬ p303) ∨ (¬ p387))
    (h24517 : (¬ p10) ∨ p387 ∨ (¬ p996)) : (¬ p10) ∨ p419 ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u4 : (¬ p387) := by
    rcases h26866 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h24517 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u3)

theorem step34035 (p495 p633 p636 p1229 : Prop)
    (h26885 : p636 ∨ p633)
    (h24273 : (¬ p636) ∨ (¬ p495) ∨ (¬ p1229)) : p633 ∨ (¬ p495) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h24273 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)

#print axioms step34035

end NineRUPTrial
