import Mathlib.Tactic.Tauto

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineRUPTrial

theorem step20207 (p2 p7 p127 p435 p788 p1542 p1563 : Prop)
    (h16152 : (¬ p7))
    (h5066 : p788)
    (h16434 : (¬ p1563))
    (h15670 : (¬ p2) ∨ p7 ∨ (¬ p127) ∨ (¬ p435) ∨ (¬ p788) ∨ (¬ p1542) ∨ p1563) : (¬ p2) ∨ (¬ p127) ∨ (¬ p435) ∨ (¬ p1542) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p788 := by
    exact h5066
  have u6 : (¬ p1563) := by
    exact h16434
  rcases h15670 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step20208 (p2 p7 p127 p280 p434 p788 p1192 p1545 : Prop)
    (h16152 : (¬ p7))
    (h16173 : (¬ p280))
    (h5066 : p788)
    (h15671 : (¬ p2) ∨ p7 ∨ (¬ p127) ∨ p280 ∨ (¬ p434) ∨ (¬ p788) ∨ (¬ p1192) ∨ (¬ p1545)) : (¬ p2) ∨ (¬ p127) ∨ (¬ p434) ∨ (¬ p1192) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p280) := by
    exact h16173
  have u7 : p788 := by
    exact h5066
  rcases h15671 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step20209 (p7 p8 p14 p40 p85 p557 p728 p1184 p1249 p1330 p1489 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h7053 : p1184)
    (h15672 : p7 ∨ (¬ p8) ∨ (¬ p14) ∨ p40 ∨ (¬ p85) ∨ (¬ p557) ∨ (¬ p728) ∨ (¬ p1184) ∨ (¬ p1249) ∨ (¬ p1330) ∨ (¬ p1489)) : (¬ p8) ∨ (¬ p14) ∨ (¬ p85) ∨ (¬ p557) ∨ (¬ p728) ∨ (¬ p1249) ∨ (¬ p1330) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p40) := by
    exact h16150
  have u10 : p1184 := by
    exact h7053
  rcases h15672 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u9 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step20210 (p7 p158 p668 p835 p928 p1061 p1385 : Prop)
    (h16152 : (¬ p7))
    (h15673 : p7 ∨ (¬ p158) ∨ (¬ p668) ∨ (¬ p835) ∨ (¬ p928) ∨ (¬ p1061) ∨ (¬ p1385)) : (¬ p158) ∨ (¬ p668) ∨ (¬ p835) ∨ (¬ p928) ∨ (¬ p1061) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p835 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15673 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20211 (p7 p668 p835 p928 p1116 p1385 : Prop)
    (h16152 : (¬ p7))
    (h15674 : p7 ∨ (¬ p668) ∨ (¬ p835) ∨ (¬ p928) ∨ (¬ p1116) ∨ (¬ p1385)) : (¬ p668) ∨ (¬ p835) ∨ (¬ p928) ∨ (¬ p1116) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p835 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15674 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20212 (p7 p537 p738 p835 p928 p1385 : Prop)
    (h16152 : (¬ p7))
    (h15675 : p7 ∨ (¬ p537) ∨ (¬ p738) ∨ (¬ p835) ∨ (¬ p928) ∨ (¬ p1385)) : (¬ p537) ∨ (¬ p738) ∨ (¬ p835) ∨ (¬ p928) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p738 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p835 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15675 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20213 (p7 p17 p40 p279 p423 p581 p864 p1035 p1249 p1325 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h1444 : p279)
    (h15676 : p7 ∨ (¬ p17) ∨ p40 ∨ (¬ p279) ∨ (¬ p423) ∨ (¬ p581) ∨ (¬ p864) ∨ (¬ p1035) ∨ (¬ p1249) ∨ (¬ p1325)) : (¬ p17) ∨ (¬ p423) ∨ (¬ p581) ∨ (¬ p864) ∨ (¬ p1035) ∨ (¬ p1249) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p40) := by
    exact h16150
  have u9 : p279 := by
    exact h1444
  rcases h15676 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u8 q2)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step20214 (p7 p127 p788 p1159 p1255 p1273 p1385 p1527 : Prop)
    (h16152 : (¬ p7))
    (h5066 : p788)
    (h16359 : (¬ p1527))
    (h15677 : p7 ∨ (¬ p127) ∨ (¬ p788) ∨ (¬ p1159) ∨ (¬ p1255) ∨ (¬ p1273) ∨ (¬ p1385) ∨ p1527) : (¬ p127) ∨ (¬ p1159) ∨ (¬ p1255) ∨ (¬ p1273) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1255 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p788 := by
    exact h5066
  have u7 : (¬ p1527) := by
    exact h16359
  rcases h15677 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step20215 (p7 p41 p87 p185 p187 p481 p836 p904 p919 p996 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16230 : (¬ p919))
    (h6744 : p1135)
    (h15678 : p7 ∨ (¬ p41) ∨ (¬ p87) ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p481) ∨ (¬ p836) ∨ (¬ p904) ∨ p919 ∨ (¬ p996) ∨ (¬ p1135)) : (¬ p41) ∨ (¬ p87) ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p481) ∨ (¬ p836) ∨ (¬ p904) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p919) := by
    exact h16230
  have u10 : p1135 := by
    exact h6744
  rcases h15678 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (u9 q8)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u10)

theorem step20216 (p7 p17 p70 p83 p389 p481 p581 p996 p1249 p1493 : Prop)
    (h16152 : (¬ p7))
    (h15679 : p7 ∨ (¬ p17) ∨ (¬ p70) ∨ (¬ p83) ∨ (¬ p389) ∨ (¬ p481) ∨ (¬ p581) ∨ (¬ p996) ∨ (¬ p1249) ∨ (¬ p1493)) : (¬ p17) ∨ (¬ p70) ∨ (¬ p83) ∨ (¬ p389) ∨ (¬ p481) ∨ (¬ p581) ∨ (¬ p996) ∨ (¬ p1249) ∨ (¬ p1493) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1493 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15679 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20217 (p7 p14 p40 p226 p481 p996 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h6744 : p1135)
    (h15680 : p7 ∨ (¬ p14) ∨ p40 ∨ (¬ p226) ∨ (¬ p481) ∨ (¬ p996) ∨ (¬ p1135)) : (¬ p14) ∨ (¬ p226) ∨ (¬ p481) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p40) := by
    exact h16150
  have u6 : p1135 := by
    exact h6744
  rcases h15680 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step20218 (p3 p7 p17 p45 p70 p83 p129 p544 p581 p657 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h6744 : p1135)
    (h15681 : (¬ p3) ∨ p7 ∨ (¬ p17) ∨ (¬ p45) ∨ (¬ p70) ∨ (¬ p83) ∨ p129 ∨ (¬ p544) ∨ (¬ p581) ∨ (¬ p657) ∨ (¬ p1135)) : (¬ p3) ∨ (¬ p17) ∨ (¬ p45) ∨ (¬ p70) ∨ (¬ p83) ∨ (¬ p544) ∨ (¬ p581) ∨ (¬ p657) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p129) := by
    exact h16154
  have u10 : p1135 := by
    exact h6744
  rcases h15681 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u9 q6)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u10)

theorem step20219 (p7 p17 p45 p129 p581 p790 p876 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h5054 : p876)
    (h15682 : p7 ∨ (¬ p17) ∨ (¬ p45) ∨ p129 ∨ (¬ p581) ∨ (¬ p790) ∨ (¬ p876)) : (¬ p17) ∨ (¬ p45) ∨ (¬ p581) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p876 := by
    exact h5054
  rcases h15682 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step20220 (p3 p7 p17 p70 p83 p544 p581 p842 p1385 : Prop)
    (h16152 : (¬ p7))
    (h15683 : (¬ p3) ∨ p7 ∨ (¬ p17) ∨ (¬ p70) ∨ (¬ p83) ∨ (¬ p544) ∨ (¬ p581) ∨ (¬ p842) ∨ (¬ p1385)) : (¬ p3) ∨ (¬ p17) ∨ (¬ p70) ∨ (¬ p83) ∨ (¬ p544) ∨ (¬ p581) ∨ (¬ p842) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p842 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15683 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20221 (p7 p45 p129 p224 p343 p406 p816 p1393 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h1950 : p343)
    (h15684 : p7 ∨ (¬ p45) ∨ p129 ∨ (¬ p224) ∨ (¬ p343) ∨ (¬ p406) ∨ (¬ p816) ∨ (¬ p1393)) : (¬ p45) ∨ (¬ p224) ∨ (¬ p406) ∨ (¬ p816) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p343 := by
    exact h1950
  rcases h15684 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step20222 (p7 p13 p161 p710 p904 p919 p1061 p1184 p1232 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16230 : (¬ p919))
    (h7053 : p1184)
    (h15685 : p7 ∨ (¬ p13) ∨ (¬ p161) ∨ (¬ p710) ∨ (¬ p904) ∨ p919 ∨ (¬ p1061) ∨ (¬ p1184) ∨ (¬ p1232) ∨ (¬ p1452)) : (¬ p13) ∨ (¬ p161) ∨ (¬ p710) ∨ (¬ p904) ∨ (¬ p1061) ∨ (¬ p1232) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p919) := by
    exact h16230
  have u9 : p1184 := by
    exact h7053
  rcases h15685 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u8 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step20223 (p280 p327 p996 p1135 : Prop)
    (h16173 : (¬ p280))
    (h6744 : p1135)
    (h15686 : p280 ∨ p327 ∨ (¬ p996) ∨ (¬ p1135)) : p327 ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p327) := fun hu => hn (Or.inl hu)
  have u1 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p280) := by
    exact h16173
  have u3 : p1135 := by
    exact h6744
  rcases h15686 with q0 | q1 | q2 | q3
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)

theorem step20224 (p7 p10 p27 p438 p600 p1542 : Prop)
    (h16152 : (¬ p7))
    (h15688 : p7 ∨ (¬ p10) ∨ (¬ p27) ∨ (¬ p438) ∨ (¬ p600) ∨ (¬ p1542)) : (¬ p10) ∨ (¬ p27) ∨ (¬ p438) ∨ (¬ p600) ∨ (¬ p1542) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p27 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p600 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15688 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20225 (p7 p41 p87 p187 p431 p481 p814 p996 p1015 : Prop)
    (h16152 : (¬ p7))
    (h15690 : p7 ∨ (¬ p41) ∨ (¬ p87) ∨ (¬ p187) ∨ (¬ p431) ∨ (¬ p481) ∨ (¬ p814) ∨ (¬ p996) ∨ (¬ p1015)) : (¬ p41) ∨ (¬ p87) ∨ (¬ p187) ∨ (¬ p431) ∨ (¬ p481) ∨ (¬ p814) ∨ (¬ p996) ∨ (¬ p1015) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15690 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20226 (p7 p258 p279 p576 p686 p1273 p1349 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16205 : (¬ p686))
    (h15691 : p7 ∨ (¬ p258) ∨ (¬ p279) ∨ (¬ p576) ∨ p686 ∨ (¬ p1273) ∨ (¬ p1349)) : (¬ p258) ∨ (¬ p576) ∨ (¬ p1273) ∨ (¬ p1349) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p279 := by
    exact h1444
  have u6 : (¬ p686) := by
    exact h16205
  rcases h15691 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step20227 (p7 p224 p814 p842 p861 p1346 : Prop)
    (h16152 : (¬ p7))
    (h15692 : p7 ∨ (¬ p224) ∨ (¬ p814) ∨ (¬ p842) ∨ (¬ p861) ∨ (¬ p1346)) : (¬ p224) ∨ (¬ p814) ∨ (¬ p842) ∨ (¬ p861) ∨ (¬ p1346) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p842 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p861 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15692 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20228 (p7 p258 p519 p616 p686 p1022 p1184 p1545 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h7053 : p1184)
    (h15693 : p7 ∨ (¬ p258) ∨ (¬ p519) ∨ (¬ p616) ∨ p686 ∨ (¬ p1022) ∨ (¬ p1184) ∨ (¬ p1545)) : (¬ p258) ∨ (¬ p519) ∨ (¬ p616) ∨ (¬ p1022) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p519 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p686) := by
    exact h16205
  have u7 : p1184 := by
    exact h7053
  rcases h15693 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step20229 (p7 p10 p121 p383 p431 p438 : Prop)
    (h16152 : (¬ p7))
    (h15695 : p7 ∨ (¬ p10) ∨ (¬ p121) ∨ (¬ p383) ∨ (¬ p431) ∨ (¬ p438)) : (¬ p10) ∨ (¬ p121) ∨ (¬ p383) ∨ (¬ p431) ∨ (¬ p438) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p383 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15695 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20230 (p7 p39 p69 p89 p1249 p1346 : Prop)
    (h16152 : (¬ p7))
    (h15696 : p7 ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p89) ∨ (¬ p1249) ∨ (¬ p1346)) : (¬ p39) ∨ (¬ p69) ∨ (¬ p89) ∨ (¬ p1249) ∨ (¬ p1346) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15696 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20231 (p7 p104 p124 p263 p544 p728 p1330 p1349 p1489 : Prop)
    (h16152 : (¬ p7))
    (h15697 : p7 ∨ (¬ p104) ∨ (¬ p124) ∨ (¬ p263) ∨ (¬ p544) ∨ (¬ p728) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p1489)) : (¬ p104) ∨ (¬ p124) ∨ (¬ p263) ∨ (¬ p544) ∨ (¬ p728) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p263 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15697 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20234 (p3 p7 p70 p431 p544 p616 p657 p1545 : Prop)
    (h16152 : (¬ p7))
    (h15700 : (¬ p3) ∨ p7 ∨ (¬ p70) ∨ (¬ p431) ∨ (¬ p544) ∨ (¬ p616) ∨ (¬ p657) ∨ (¬ p1545)) : (¬ p3) ∨ (¬ p70) ∨ (¬ p431) ∨ (¬ p544) ∨ (¬ p616) ∨ (¬ p657) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15700 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20237 (p7 p17 p41 p87 p187 p389 p456 p481 p579 p996 : Prop)
    (h16152 : (¬ p7))
    (h15704 : p7 ∨ (¬ p17) ∨ (¬ p41) ∨ (¬ p87) ∨ (¬ p187) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p481) ∨ (¬ p579) ∨ (¬ p996)) : (¬ p17) ∨ (¬ p41) ∨ (¬ p87) ∨ (¬ p187) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p481) ∨ (¬ p579) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15704 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20238 (p7 p45 p129 p406 p431 p734 p816 p897 p1099 p1184 p1393 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h7053 : p1184)
    (h15705 : p7 ∨ (¬ p45) ∨ p129 ∨ (¬ p406) ∨ (¬ p431) ∨ (¬ p734) ∨ (¬ p816) ∨ (¬ p897) ∨ (¬ p1099) ∨ (¬ p1184) ∨ (¬ p1393)) : (¬ p45) ∨ (¬ p406) ∨ (¬ p431) ∨ (¬ p734) ∨ (¬ p816) ∨ (¬ p897) ∨ (¬ p1099) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p129) := by
    exact h16154
  have u10 : p1184 := by
    exact h7053
  rcases h15705 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u9 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u10)
  · exact False.elim (q10 u7)

theorem step20239 (p7 p45 p129 p158 p346 p495 p636 p668 p928 p1061 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h7053 : p1184)
    (h15706 : p7 ∨ (¬ p45) ∨ p129 ∨ (¬ p158) ∨ (¬ p346) ∨ (¬ p495) ∨ (¬ p636) ∨ (¬ p668) ∨ (¬ p928) ∨ (¬ p1061) ∨ (¬ p1184)) : (¬ p45) ∨ (¬ p158) ∨ (¬ p346) ∨ (¬ p495) ∨ (¬ p636) ∨ (¬ p668) ∨ (¬ p928) ∨ (¬ p1061) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p129) := by
    exact h16154
  have u10 : p1184 := by
    exact h7053
  rcases h15706 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u9 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u10)

theorem step20240 (p7 p13 p45 p129 p158 p161 p928 p1061 p1184 p1232 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h7053 : p1184)
    (h15707 : p7 ∨ (¬ p13) ∨ (¬ p45) ∨ p129 ∨ (¬ p158) ∨ (¬ p161) ∨ (¬ p928) ∨ (¬ p1061) ∨ (¬ p1184) ∨ (¬ p1232) ∨ (¬ p1452)) : (¬ p13) ∨ (¬ p45) ∨ (¬ p158) ∨ (¬ p161) ∨ (¬ p928) ∨ (¬ p1061) ∨ (¬ p1232) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p129) := by
    exact h16154
  have u10 : p1184 := by
    exact h7053
  rcases h15707 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u9 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step20241 (p40 p234 p326 p788 : Prop)
    (h16150 : (¬ p40))
    (h5066 : p788)
    (h15708 : p40 ∨ (¬ p234) ∨ p326 ∨ (¬ p788)) : (¬ p234) ∨ p326 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p326) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p40) := by
    exact h16150
  have u3 : p788 := by
    exact h5066
  rcases h15708 with q0 | q1 | q2 | q3
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)

theorem step20243 (p7 p258 p308 p1055 p1082 p1443 : Prop)
    (h16152 : (¬ p7))
    (h15710 : p7 ∨ (¬ p258) ∨ (¬ p308) ∨ (¬ p1055) ∨ (¬ p1082) ∨ (¬ p1443)) : (¬ p258) ∨ (¬ p308) ∨ (¬ p1055) ∨ (¬ p1082) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p308 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1082 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15710 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20244 (p7 p346 p426 p1074 p1077 p1099 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h7053 : p1184)
    (h15711 : p7 ∨ (¬ p346) ∨ p426 ∨ (¬ p1074) ∨ (¬ p1077) ∨ (¬ p1099) ∨ (¬ p1184)) : (¬ p346) ∨ (¬ p1074) ∨ (¬ p1077) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p426) := by
    exact h16178
  have u6 : p1184 := by
    exact h7053
  rcases h15711 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step20245 (p7 p127 p134 p186 p799 p814 : Prop)
    (h16152 : (¬ p7))
    (h15712 : p7 ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p186) ∨ (¬ p799) ∨ (¬ p814)) : (¬ p127) ∨ (¬ p134) ∨ (¬ p186) ∨ (¬ p799) ∨ (¬ p814) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p799 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15712 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20246 (p7 p142 p193 p326 p798 p814 : Prop)
    (h16152 : (¬ p7))
    (h15713 : p7 ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p326) ∨ (¬ p798) ∨ (¬ p814)) : (¬ p142) ∨ (¬ p193) ∨ (¬ p326) ∨ (¬ p798) ∨ (¬ p814) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p798 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15713 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20247 (p7 p308 p426 p455 p636 p681 p897 p961 p1055 p1095 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h3892 : p681)
    (h15714 : p7 ∨ (¬ p308) ∨ p426 ∨ (¬ p455) ∨ (¬ p636) ∨ (¬ p681) ∨ (¬ p897) ∨ (¬ p961) ∨ (¬ p1055) ∨ (¬ p1095)) : (¬ p308) ∨ (¬ p455) ∨ (¬ p636) ∨ (¬ p897) ∨ (¬ p961) ∨ (¬ p1055) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p308 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p426) := by
    exact h16178
  have u9 : p681 := by
    exact h3892
  rcases h15714 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u8 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step20248 (p7 p86 p346 p426 p495 p636 p789 p790 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h8348 : p1386)
    (h15715 : p7 ∨ (¬ p86) ∨ (¬ p346) ∨ p426 ∨ (¬ p495) ∨ (¬ p636) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p86) ∨ (¬ p346) ∨ (¬ p495) ∨ (¬ p636) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p426) := by
    exact h16178
  have u9 : p1386 := by
    exact h8348
  rcases h15715 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u8 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u9)

theorem step20249 (p7 p40 p142 p234 p476 p687 p788 p797 p1015 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h5066 : p788)
    (h15716 : p7 ∨ p40 ∨ (¬ p142) ∨ (¬ p234) ∨ (¬ p476) ∨ (¬ p687) ∨ (¬ p788) ∨ (¬ p797) ∨ (¬ p1015)) : (¬ p142) ∨ (¬ p234) ∨ (¬ p476) ∨ (¬ p687) ∨ (¬ p797) ∨ (¬ p1015) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p476 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p797 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p40) := by
    exact h16150
  have u8 : p788 := by
    exact h5066
  rcases h15716 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step20250 (p7 p86 p495 p636 p669 p789 p790 p1076 : Prop)
    (h16152 : (¬ p7))
    (h15717 : p7 ∨ (¬ p86) ∨ (¬ p495) ∨ (¬ p636) ∨ (¬ p669) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1076)) : (¬ p86) ∨ (¬ p495) ∨ (¬ p636) ∨ (¬ p669) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15717 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20251 (p7 p86 p304 p389 p456 p494 p633 p789 p790 : Prop)
    (h16152 : (¬ p7))
    (h15718 : p7 ∨ (¬ p86) ∨ (¬ p304) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p494) ∨ (¬ p633) ∨ (¬ p789) ∨ (¬ p790)) : (¬ p86) ∨ (¬ p304) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p494) ∨ (¬ p633) ∨ (¬ p789) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15718 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20252 (p4 p7 p420 p633 p738 p756 : Prop)
    (h16152 : (¬ p7))
    (h15719 : (¬ p4) ∨ p7 ∨ (¬ p420) ∨ (¬ p633) ∨ (¬ p738) ∨ (¬ p756)) : (¬ p4) ∨ (¬ p420) ∨ (¬ p633) ∨ (¬ p738) ∨ (¬ p756) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p738 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15719 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20253 (p2 p7 p40 p161 p234 p983 p1040 p1140 p1184 p1232 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h7053 : p1184)
    (h15720 : (¬ p2) ∨ p7 ∨ p40 ∨ (¬ p161) ∨ (¬ p234) ∨ (¬ p983) ∨ (¬ p1040) ∨ (¬ p1140) ∨ (¬ p1184) ∨ (¬ p1232)) : (¬ p2) ∨ (¬ p161) ∨ (¬ p234) ∨ (¬ p983) ∨ (¬ p1040) ∨ (¬ p1140) ∨ (¬ p1232) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1040 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p40) := by
    exact h16150
  have u9 : p1184 := by
    exact h7053
  rcases h15720 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (u8 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u9)
  · exact False.elim (q9 u6)

theorem step20254 (p2 p7 p211 p227 p326 p1206 : Prop)
    (h16152 : (¬ p7))
    (h15721 : (¬ p2) ∨ p7 ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p326) ∨ (¬ p1206)) : (¬ p2) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p326) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15721 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20256 (p7 p105 p142 p192 p544 p556 p710 : Prop)
    (h16152 : (¬ p7))
    (h15723 : p7 ∨ (¬ p105) ∨ (¬ p142) ∨ (¬ p192) ∨ (¬ p544) ∨ (¬ p556) ∨ (¬ p710)) : (¬ p105) ∨ (¬ p142) ∨ (¬ p192) ∨ (¬ p544) ∨ (¬ p556) ∨ (¬ p710) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15723 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20257 (p7 p42 p68 p127 p134 p225 p229 p426 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16178 : (¬ p426))
    (h15724 : p7 ∨ (¬ p42) ∨ (¬ p68) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p225) ∨ (¬ p229) ∨ p426) : (¬ p68) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p225) ∨ (¬ p229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p426) := by
    exact h16178
  rcases h15724 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step20258 (p7 p42 p127 p134 p544 p556 p653 p710 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16194 : (¬ p653))
    (h15725 : p7 ∨ (¬ p42) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p544) ∨ (¬ p556) ∨ p653 ∨ (¬ p710)) : (¬ p127) ∨ (¬ p134) ∨ (¬ p544) ∨ (¬ p556) ∨ (¬ p710) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p653) := by
    exact h16194
  rcases h15725 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step20259 (p7 p8 p105 p142 p165 p557 p836 : Prop)
    (h16152 : (¬ p7))
    (h15726 : p7 ∨ (¬ p8) ∨ (¬ p105) ∨ (¬ p142) ∨ (¬ p165) ∨ (¬ p557) ∨ (¬ p836)) : (¬ p8) ∨ (¬ p105) ∨ (¬ p142) ∨ (¬ p165) ∨ (¬ p557) ∨ (¬ p836) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p165 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15726 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20260 (p7 p8 p42 p127 p134 p682 p836 p1044 p1116 p1159 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16203 : (¬ p682))
    (h15727 : p7 ∨ (¬ p8) ∨ (¬ p42) ∨ (¬ p127) ∨ (¬ p134) ∨ p682 ∨ (¬ p836) ∨ (¬ p1044) ∨ (¬ p1116) ∨ (¬ p1159)) : (¬ p8) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p836) ∨ (¬ p1044) ∨ (¬ p1116) ∨ (¬ p1159) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p42 := by
    exact h132
  have u9 : (¬ p682) := by
    exact h16203
  rcases h15727 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u9 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step20261 (p7 p86 p495 p789 p790 p1333 p1454 p1604 : Prop)
    (h16152 : (¬ p7))
    (h15728 : p7 ∨ (¬ p86) ∨ (¬ p495) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1333) ∨ (¬ p1454) ∨ (¬ p1604)) : (¬ p86) ∨ (¬ p495) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1333) ∨ (¬ p1454) ∨ (¬ p1604) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1454 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1604 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15728 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20262 (p7 p42 p127 p134 p349 p434 p477 p686 p690 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16205 : (¬ p686))
    (h15729 : p7 ∨ (¬ p42) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p349) ∨ (¬ p434) ∨ (¬ p477) ∨ p686 ∨ (¬ p690)) : (¬ p127) ∨ (¬ p134) ∨ (¬ p349) ∨ (¬ p434) ∨ (¬ p477) ∨ (¬ p690) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p477 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : p42 := by
    exact h132
  have u8 : (¬ p686) := by
    exact h16205
  rcases h15729 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u8 q7)
  · exact False.elim (q8 u5)

theorem step20263 (p7 p86 p389 p456 p495 p1325 p1346 p1508 : Prop)
    (h16152 : (¬ p7))
    (h15730 : p7 ∨ (¬ p86) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p1325) ∨ (¬ p1346) ∨ (¬ p1508)) : (¬ p86) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p1325) ∨ (¬ p1346) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15730 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20264 (p7 p42 p68 p127 p134 p532 p1141 p1208 p1324 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16309 : (¬ p1324))
    (h15731 : p7 ∨ (¬ p42) ∨ (¬ p68) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p532) ∨ (¬ p1141) ∨ (¬ p1208) ∨ p1324) : (¬ p68) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p532) ∨ (¬ p1141) ∨ (¬ p1208) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1208 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : p42 := by
    exact h132
  have u8 : (¬ p1324) := by
    exact h16309
  rcases h15731 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u8 q8)

theorem step20265 (p7 p406 p444 p495 p617 p858 p1022 p1604 : Prop)
    (h16152 : (¬ p7))
    (h15732 : p7 ∨ (¬ p406) ∨ (¬ p444) ∨ (¬ p495) ∨ (¬ p617) ∨ (¬ p858) ∨ (¬ p1022) ∨ (¬ p1604)) : (¬ p406) ∨ (¬ p444) ∨ (¬ p495) ∨ (¬ p617) ∨ (¬ p858) ∨ (¬ p1022) ∨ (¬ p1604) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p444 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1604 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15732 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20267 (p7 p42 p68 p127 p134 p237 p791 p983 p1116 p1473 p1710 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16213 : (¬ p791))
    (h15734 : p7 ∨ (¬ p42) ∨ (¬ p68) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p237) ∨ p791 ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1473) ∨ (¬ p1710)) : (¬ p68) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p237) ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1473) ∨ (¬ p1710) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1473 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p42 := by
    exact h132
  have u10 : (¬ p791) := by
    exact h16213
  rcases h15734 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u10 q6)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step20268 (p2 p3 p7 p544 p545 : Prop)
    (h16152 : (¬ p7))
    (h15735 : (¬ p2) ∨ (¬ p3) ∨ p7 ∨ (¬ p544) ∨ (¬ p545)) : (¬ p2) ∨ (¬ p3) ∨ (¬ p544) ∨ (¬ p545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  rcases h15735 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u4 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)

theorem step20269 (p7 p84 p186 p481 p499 p582 p796 p1148 p1232 p1256 : Prop)
    (h16152 : (¬ p7))
    (h15736 : p7 ∨ (¬ p84) ∨ (¬ p186) ∨ (¬ p481) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p796) ∨ (¬ p1148) ∨ (¬ p1232) ∨ (¬ p1256)) : (¬ p84) ∨ (¬ p186) ∨ (¬ p481) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p796) ∨ (¬ p1148) ∨ (¬ p1232) ∨ (¬ p1256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1148 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15736 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20270 (p7 p193 p267 p424 p532 p961 p1330 p1366 : Prop)
    (h16152 : (¬ p7))
    (h15737 : p7 ∨ (¬ p193) ∨ (¬ p267) ∨ (¬ p424) ∨ (¬ p532) ∨ (¬ p961) ∨ (¬ p1330) ∨ (¬ p1366)) : (¬ p193) ∨ (¬ p267) ∨ (¬ p424) ∨ (¬ p532) ∨ (¬ p961) ∨ (¬ p1330) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p267 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15737 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20271 (p7 p886 p1036 p1099 p1229 p1310 : Prop)
    (h16152 : (¬ p7))
    (h15738 : p7 ∨ (¬ p886) ∨ (¬ p1036) ∨ (¬ p1099) ∨ (¬ p1229) ∨ (¬ p1310)) : (¬ p886) ∨ (¬ p1036) ∨ (¬ p1099) ∨ (¬ p1229) ∨ (¬ p1310) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p886 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15738 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20272 (p7 p84 p224 p499 p582 p616 p789 p790 p906 : Prop)
    (h16152 : (¬ p7))
    (h15739 : p7 ∨ (¬ p84) ∨ (¬ p224) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p616) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p906)) : (¬ p84) ∨ (¬ p224) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p616) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p906) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p906 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15739 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20273 (p7 p84 p142 p186 p430 p481 p499 p582 p616 p788 p796 p1545 : Prop)
    (h16152 : (¬ p7))
    (h16180 : (¬ p430))
    (h5066 : p788)
    (h15740 : p7 ∨ (¬ p84) ∨ (¬ p142) ∨ (¬ p186) ∨ p430 ∨ (¬ p481) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p616) ∨ (¬ p788) ∨ (¬ p796) ∨ (¬ p1545)) : (¬ p84) ∨ (¬ p142) ∨ (¬ p186) ∨ (¬ p481) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p616) ∨ (¬ p796) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p430) := by
    exact h16180
  have u11 : p788 := by
    exact h5066
  rcases h15740 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u10 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u11)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step20274 (p7 p105 p142 p226 p481 p796 : Prop)
    (h16152 : (¬ p7))
    (h15741 : p7 ∨ (¬ p105) ∨ (¬ p142) ∨ (¬ p226) ∨ (¬ p481) ∨ (¬ p796)) : (¬ p105) ∨ (¬ p142) ∨ (¬ p226) ∨ (¬ p481) ∨ (¬ p796) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15741 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20275 (p7 p237 p267 p532 p728 p840 p961 p1330 : Prop)
    (h16152 : (¬ p7))
    (h15742 : p7 ∨ (¬ p237) ∨ (¬ p267) ∨ (¬ p532) ∨ (¬ p728) ∨ (¬ p840) ∨ (¬ p961) ∨ (¬ p1330)) : (¬ p237) ∨ (¬ p267) ∨ (¬ p532) ∨ (¬ p728) ∨ (¬ p840) ∨ (¬ p961) ∨ (¬ p1330) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p267 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15742 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20276 (p7 p84 p499 p582 p1232 p1295 p1325 p1346 p1508 : Prop)
    (h16152 : (¬ p7))
    (h15743 : p7 ∨ (¬ p84) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p1232) ∨ (¬ p1295) ∨ (¬ p1325) ∨ (¬ p1346) ∨ (¬ p1508)) : (¬ p84) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p1232) ∨ (¬ p1295) ∨ (¬ p1325) ∨ (¬ p1346) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1295 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15743 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20277 (p7 p84 p193 p304 p424 p425 p582 p669 p996 p1076 : Prop)
    (h16152 : (¬ p7))
    (h15744 : p7 ∨ (¬ p84) ∨ (¬ p193) ∨ (¬ p304) ∨ (¬ p424) ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p669) ∨ (¬ p996) ∨ (¬ p1076)) : (¬ p84) ∨ (¬ p193) ∨ (¬ p304) ∨ (¬ p424) ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p669) ∨ (¬ p996) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15744 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20278 (p7 p267 p304 p726 p789 p790 p985 p1333 : Prop)
    (h16152 : (¬ p7))
    (h15745 : p7 ∨ (¬ p267) ∨ (¬ p304) ∨ (¬ p726) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p985) ∨ (¬ p1333)) : (¬ p267) ∨ (¬ p304) ∨ (¬ p726) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p985) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p267 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15745 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20279 (p7 p186 p267 p304 p481 p796 p1040 p1076 p1256 : Prop)
    (h16152 : (¬ p7))
    (h15746 : p7 ∨ (¬ p186) ∨ (¬ p267) ∨ (¬ p304) ∨ (¬ p481) ∨ (¬ p796) ∨ (¬ p1040) ∨ (¬ p1076) ∨ (¬ p1256)) : (¬ p186) ∨ (¬ p267) ∨ (¬ p304) ∨ (¬ p481) ∨ (¬ p796) ∨ (¬ p1040) ∨ (¬ p1076) ∨ (¬ p1256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p267 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1040 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15746 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20281 (p7 p84 p106 p163 p186 p481 p756 p796 p929 p1538 : Prop)
    (h16152 : (¬ p7))
    (h15749 : p7 ∨ (¬ p84) ∨ (¬ p106) ∨ (¬ p163) ∨ (¬ p186) ∨ (¬ p481) ∨ (¬ p756) ∨ (¬ p796) ∨ (¬ p929) ∨ (¬ p1538)) : (¬ p84) ∨ (¬ p106) ∨ (¬ p163) ∨ (¬ p186) ∨ (¬ p481) ∨ (¬ p756) ∨ (¬ p796) ∨ (¬ p929) ∨ (¬ p1538) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15749 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20283 (p7 p161 p499 p983 p1181 p1232 p1530 : Prop)
    (h16152 : (¬ p7))
    (h16272 : (¬ p1181))
    (h9352 : p1530)
    (h15751 : p7 ∨ (¬ p161) ∨ (¬ p499) ∨ (¬ p983) ∨ p1181 ∨ (¬ p1232) ∨ (¬ p1530)) : (¬ p161) ∨ (¬ p499) ∨ (¬ p983) ∨ (¬ p1232) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p1181) := by
    exact h16272
  have u6 : p1530 := by
    exact h9352
  rcases h15751 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step20284 (p7 p84 p193 p424 p499 p582 p996 p1232 p1295 : Prop)
    (h16152 : (¬ p7))
    (h15752 : p7 ∨ (¬ p84) ∨ (¬ p193) ∨ (¬ p424) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p996) ∨ (¬ p1232) ∨ (¬ p1295)) : (¬ p84) ∨ (¬ p193) ∨ (¬ p424) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p996) ∨ (¬ p1232) ∨ (¬ p1295) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1295 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15752 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20285 (p7 p84 p193 p305 p346 p424 p425 p426 p582 p996 p1055 p1077 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h6744 : p1135)
    (h15753 : p7 ∨ (¬ p84) ∨ (¬ p193) ∨ (¬ p305) ∨ (¬ p346) ∨ (¬ p424) ∨ (¬ p425) ∨ p426 ∨ (¬ p582) ∨ (¬ p996) ∨ (¬ p1055) ∨ (¬ p1077) ∨ (¬ p1135)) : (¬ p84) ∨ (¬ p193) ∨ (¬ p305) ∨ (¬ p346) ∨ (¬ p424) ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p996) ∨ (¬ p1055) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : (¬ p426) := by
    exact h16178
  have u12 : p1135 := by
    exact h6744
  rcases h15753 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u11 q7)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u8)
  · exact False.elim (q11 u9)
  · exact False.elim (q12 u12)

theorem step20286 (p7 p84 p193 p346 p424 p499 p542 p582 p635 p1099 : Prop)
    (h16152 : (¬ p7))
    (h15755 : p7 ∨ (¬ p84) ∨ (¬ p193) ∨ (¬ p346) ∨ (¬ p424) ∨ (¬ p499) ∨ (¬ p542) ∨ (¬ p582) ∨ (¬ p635) ∨ (¬ p1099)) : (¬ p84) ∨ (¬ p193) ∨ (¬ p346) ∨ (¬ p424) ∨ (¬ p499) ∨ (¬ p542) ∨ (¬ p582) ∨ (¬ p635) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p635 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15755 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20287 (p7 p48 p68 p142 p346 p426 p481 p499 p582 p635 p788 p796 p1099 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h5066 : p788)
    (h15756 : p7 ∨ (¬ p48) ∨ (¬ p68) ∨ (¬ p142) ∨ (¬ p346) ∨ p426 ∨ (¬ p481) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p635) ∨ (¬ p788) ∨ (¬ p796) ∨ (¬ p1099)) : (¬ p48) ∨ (¬ p68) ∨ (¬ p142) ∨ (¬ p346) ∨ (¬ p481) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p635) ∨ (¬ p796) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p635 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : (¬ p426) := by
    exact h16178
  have u12 : p788 := by
    exact h5066
  rcases h15756 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u11 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u12)
  · exact False.elim (q11 u8)
  · exact False.elim (q12 u9)

theorem step20289 (p7 p70 p142 p346 p426 p481 p495 p636 p788 p796 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h5066 : p788)
    (h15758 : p7 ∨ (¬ p70) ∨ (¬ p142) ∨ (¬ p346) ∨ p426 ∨ (¬ p481) ∨ (¬ p495) ∨ (¬ p636) ∨ (¬ p788) ∨ (¬ p796)) : (¬ p70) ∨ (¬ p142) ∨ (¬ p346) ∨ (¬ p481) ∨ (¬ p495) ∨ (¬ p636) ∨ (¬ p796) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p426) := by
    exact h16178
  have u9 : p788 := by
    exact h5066
  rcases h15758 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u8 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u9)
  · exact False.elim (q9 u6)

theorem step20290 (p7 p45 p135 p265 p304 p580 p633 : Prop)
    (h16152 : (¬ p7))
    (h15759 : p7 ∨ (¬ p45) ∨ (¬ p135) ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p580) ∨ (¬ p633)) : (¬ p45) ∨ (¬ p135) ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p580) ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15759 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20291 (p7 p171 p189 p242 p1061 p1115 : Prop)
    (h16152 : (¬ p7))
    (h15760 : p7 ∨ (¬ p171) ∨ (¬ p189) ∨ (¬ p242) ∨ (¬ p1061) ∨ (¬ p1115)) : (¬ p171) ∨ (¬ p189) ∨ (¬ p242) ∨ (¬ p1061) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15760 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20292 (p7 p45 p84 p135 p265 p421 p431 p634 p734 p790 p801 p897 p996 : Prop)
    (h16152 : (¬ p7))
    (h15762 : p7 ∨ (¬ p45) ∨ (¬ p84) ∨ (¬ p135) ∨ (¬ p265) ∨ (¬ p421) ∨ (¬ p431) ∨ (¬ p634) ∨ (¬ p734) ∨ (¬ p790) ∨ (¬ p801) ∨ (¬ p897) ∨ (¬ p996)) : (¬ p45) ∨ (¬ p84) ∨ (¬ p135) ∨ (¬ p265) ∨ (¬ p421) ∨ (¬ p431) ∨ (¬ p634) ∨ (¬ p734) ∨ (¬ p790) ∨ (¬ p801) ∨ (¬ p897) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p634 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p801 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))
  have u12 : (¬ p7) := by
    exact h16152
  rcases h15762 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (u12 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)
  · exact False.elim (q10 u9)
  · exact False.elim (q11 u10)
  · exact False.elim (q12 u11)

theorem step20293 (p7 p41 p187 p230 p304 p389 p456 p481 p633 p681 p996 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h3892 : p681)
    (h15763 : p7 ∨ (¬ p41) ∨ (¬ p187) ∨ p230 ∨ (¬ p304) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p481) ∨ (¬ p633) ∨ (¬ p681) ∨ (¬ p996)) : (¬ p41) ∨ (¬ p187) ∨ (¬ p304) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p481) ∨ (¬ p633) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p230) := by
    exact h16165
  have u10 : p681 := by
    exact h3892
  rcases h15763 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u9 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u10)
  · exact False.elim (q10 u7)

theorem step20294 (p4 p7 p306 p420 p633 p668 p1061 : Prop)
    (h16152 : (¬ p7))
    (h15765 : (¬ p4) ∨ p7 ∨ (¬ p306) ∨ (¬ p420) ∨ (¬ p633) ∨ (¬ p668) ∨ (¬ p1061)) : (¬ p4) ∨ (¬ p306) ∨ (¬ p420) ∨ (¬ p633) ∨ (¬ p668) ∨ (¬ p1061) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15765 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20295 (p7 p45 p171 p241 p710 p904 p927 : Prop)
    (h16152 : (¬ p7))
    (h15766 : p7 ∨ (¬ p45) ∨ (¬ p171) ∨ (¬ p241) ∨ (¬ p710) ∨ (¬ p904) ∨ (¬ p927)) : (¬ p45) ∨ (¬ p171) ∨ (¬ p241) ∨ (¬ p710) ∨ (¬ p904) ∨ (¬ p927) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15766 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20297 (p7 p42 p134 p210 p456 p1445 p1611 p1624 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16350 : (¬ p1445))
    (h15768 : p7 ∨ (¬ p42) ∨ (¬ p134) ∨ (¬ p210) ∨ (¬ p456) ∨ p1445 ∨ (¬ p1611) ∨ (¬ p1624)) : (¬ p134) ∨ (¬ p210) ∨ (¬ p456) ∨ (¬ p1611) ∨ (¬ p1624) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1611 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p1445) := by
    exact h16350
  rcases h15768 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u7 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step20298 (p7 p27 p70 p142 p304 p481 p494 p633 p796 : Prop)
    (h16152 : (¬ p7))
    (h15769 : p7 ∨ (¬ p27) ∨ (¬ p70) ∨ (¬ p142) ∨ (¬ p304) ∨ (¬ p481) ∨ (¬ p494) ∨ (¬ p633) ∨ (¬ p796)) : (¬ p27) ∨ (¬ p70) ∨ (¬ p142) ∨ (¬ p304) ∨ (¬ p481) ∨ (¬ p494) ∨ (¬ p633) ∨ (¬ p796) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p27 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15769 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20299 (p7 p11 p17 p237 p286 p1080 : Prop)
    (h16152 : (¬ p7))
    (h15770 : p7 ∨ (¬ p11) ∨ (¬ p17) ∨ (¬ p237) ∨ (¬ p286) ∨ (¬ p1080)) : (¬ p11) ∨ (¬ p17) ∨ (¬ p237) ∨ (¬ p286) ∨ (¬ p1080) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15770 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20300 (p7 p141 p171 p237 p261 p961 p1443 : Prop)
    (h16152 : (¬ p7))
    (h15771 : p7 ∨ (¬ p141) ∨ (¬ p171) ∨ (¬ p237) ∨ (¬ p261) ∨ (¬ p961) ∨ (¬ p1443)) : (¬ p141) ∨ (¬ p171) ∨ (¬ p237) ∨ (¬ p261) ∨ (¬ p961) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15771 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20301 (p6 p7 p101 p194 p669 p789 p790 p1076 : Prop)
    (h16152 : (¬ p7))
    (h15772 : (¬ p6) ∨ p7 ∨ (¬ p101) ∨ (¬ p194) ∨ (¬ p669) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1076)) : (¬ p6) ∨ (¬ p101) ∨ (¬ p194) ∨ (¬ p669) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15772 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20302 (p6 p7 p101 p194 p346 p406 p820 p838 p858 : Prop)
    (h16152 : (¬ p7))
    (h15773 : (¬ p6) ∨ p7 ∨ (¬ p101) ∨ (¬ p194) ∨ (¬ p346) ∨ (¬ p406) ∨ (¬ p820) ∨ (¬ p838) ∨ (¬ p858)) : (¬ p6) ∨ (¬ p101) ∨ (¬ p194) ∨ (¬ p346) ∨ (¬ p406) ∨ (¬ p820) ∨ (¬ p838) ∨ (¬ p858) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p820 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p838 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15773 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20303 (p7 p15 p49 p84 p237 p983 p1116 p1431 p1667 : Prop)
    (h16152 : (¬ p7))
    (h15774 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p237) ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1431) ∨ (¬ p1667)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p237) ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1431) ∨ (¬ p1667) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15774 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20304 (p6 p7 p8 p13 p194 p242 p836 p1116 p1206 : Prop)
    (h16152 : (¬ p7))
    (h15775 : (¬ p6) ∨ p7 ∨ (¬ p8) ∨ (¬ p13) ∨ (¬ p194) ∨ (¬ p242) ∨ (¬ p836) ∨ (¬ p1116) ∨ (¬ p1206)) : (¬ p6) ∨ (¬ p8) ∨ (¬ p13) ∨ (¬ p194) ∨ (¬ p242) ∨ (¬ p836) ∨ (¬ p1116) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15775 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20305 (p6 p7 p38 p49 p84 p789 p790 p1333 p1454 p1666 : Prop)
    (h16152 : (¬ p7))
    (h15777 : (¬ p6) ∨ p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1333) ∨ (¬ p1454) ∨ (¬ p1666)) : (¬ p6) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1333) ∨ (¬ p1454) ∨ (¬ p1666) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1454 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15777 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (u9 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20306 (p7 p10 p38 p49 p84 p206 p280 p789 p790 p1333 p1386 p1624 p1665 : Prop)
    (h16152 : (¬ p7))
    (h16173 : (¬ p280))
    (h8348 : p1386)
    (h15778 : p7 ∨ (¬ p10) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p206) ∨ p280 ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1333) ∨ (¬ p1386) ∨ (¬ p1624) ∨ (¬ p1665)) : (¬ p10) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p206) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1333) ∨ (¬ p1624) ∨ (¬ p1665) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : (¬ p280) := by
    exact h16173
  have u12 : p1386 := by
    exact h8348
  rcases h15778 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u11 q6)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u12)
  · exact False.elim (q11 u8)
  · exact False.elim (q12 u9)

theorem step20307 (p6 p7 p38 p49 p84 p406 p444 p820 p858 p1022 p1666 : Prop)
    (h16152 : (¬ p7))
    (h15779 : (¬ p6) ∨ p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p406) ∨ (¬ p444) ∨ (¬ p820) ∨ (¬ p858) ∨ (¬ p1022) ∨ (¬ p1666)) : (¬ p6) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p406) ∨ (¬ p444) ∨ (¬ p820) ∨ (¬ p858) ∨ (¬ p1022) ∨ (¬ p1666) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p444 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p820 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h15779 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u0)
  · exact False.elim (u10 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)
  · exact False.elim (q10 u9)

theorem step20308 (p7 p10 p194 p206 p237 p351 p840 p1624 p1665 : Prop)
    (h16152 : (¬ p7))
    (h15780 : p7 ∨ (¬ p10) ∨ (¬ p194) ∨ (¬ p206) ∨ (¬ p237) ∨ (¬ p351) ∨ (¬ p840) ∨ (¬ p1624) ∨ (¬ p1665)) : (¬ p10) ∨ (¬ p194) ∨ (¬ p206) ∨ (¬ p237) ∨ (¬ p351) ∨ (¬ p840) ∨ (¬ p1624) ∨ (¬ p1665) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15780 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20309 (p7 p15 p49 p84 p237 p668 p897 p1099 p1116 : Prop)
    (h16152 : (¬ p7))
    (h15781 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p237) ∨ (¬ p668) ∨ (¬ p897) ∨ (¬ p1099) ∨ (¬ p1116)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p237) ∨ (¬ p668) ∨ (¬ p897) ∨ (¬ p1099) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15781 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20310 (p7 p15 p49 p84 p426 p789 p790 p897 p1099 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h8348 : p1386)
    (h15782 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ p426 ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p897) ∨ (¬ p1099) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p897) ∨ (¬ p1099) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p426) := by
    exact h16178
  have u10 : p1386 := by
    exact h8348
  rcases h15782 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u9 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u10)

theorem step20311 (p7 p13 p18 p69 p86 p237 p1116 p1206 : Prop)
    (h16152 : (¬ p7))
    (h15783 : p7 ∨ (¬ p13) ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p86) ∨ (¬ p237) ∨ (¬ p1116) ∨ (¬ p1206)) : (¬ p13) ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p86) ∨ (¬ p237) ∨ (¬ p1116) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15783 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20312 (p7 p14 p64 p86 p226 p789 p790 p1004 p1141 : Prop)
    (h16152 : (¬ p7))
    (h15784 : p7 ∨ (¬ p14) ∨ (¬ p64) ∨ (¬ p86) ∨ (¬ p226) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1004) ∨ (¬ p1141)) : (¬ p14) ∨ (¬ p64) ∨ (¬ p86) ∨ (¬ p226) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1004) ∨ (¬ p1141) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15784 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20314 (p7 p64 p86 p206 p389 p456 p789 p790 p1611 p1624 : Prop)
    (h16152 : (¬ p7))
    (h15786 : p7 ∨ (¬ p64) ∨ (¬ p86) ∨ (¬ p206) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1611) ∨ (¬ p1624)) : (¬ p64) ∨ (¬ p86) ∨ (¬ p206) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1611) ∨ (¬ p1624) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1611 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15786 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20315 (p7 p18 p69 p344 p389 p667 p686 p983 p1184 p1206 p1325 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h7053 : p1184)
    (h15787 : p7 ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p344) ∨ (¬ p389) ∨ (¬ p667) ∨ p686 ∨ (¬ p983) ∨ (¬ p1184) ∨ (¬ p1206) ∨ (¬ p1325)) : (¬ p18) ∨ (¬ p69) ∨ (¬ p344) ∨ (¬ p389) ∨ (¬ p667) ∨ (¬ p983) ∨ (¬ p1206) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p686) := by
    exact h16205
  have u10 : p1184 := by
    exact h7053
  rcases h15787 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u9 q6)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step20317 (p7 p14 p160 p226 p230 p405 p659 p816 p1004 p1141 p1325 p1393 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h3753 : p659)
    (h15789 : p7 ∨ (¬ p14) ∨ (¬ p160) ∨ (¬ p226) ∨ p230 ∨ (¬ p405) ∨ (¬ p659) ∨ (¬ p816) ∨ (¬ p1004) ∨ (¬ p1141) ∨ (¬ p1325) ∨ (¬ p1393)) : (¬ p14) ∨ (¬ p160) ∨ (¬ p226) ∨ (¬ p405) ∨ (¬ p816) ∨ (¬ p1004) ∨ (¬ p1141) ∨ (¬ p1325) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p405 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p230) := by
    exact h16165
  have u11 : p659 := by
    exact h3753
  rcases h15789 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u10 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step20318 (p7 p10 p18 p69 p406 p517 p617 p858 : Prop)
    (h16152 : (¬ p7))
    (h15791 : p7 ∨ (¬ p10) ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p406) ∨ (¬ p517) ∨ (¬ p617) ∨ (¬ p858)) : (¬ p10) ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p406) ∨ (¬ p517) ∨ (¬ p617) ∨ (¬ p858) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p517 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15791 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20319 (p6 p7 p19 p64 p710 p904 p919 p1044 p1061 p1141 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16230 : (¬ p919))
    (h7053 : p1184)
    (h15792 : (¬ p6) ∨ p7 ∨ (¬ p19) ∨ (¬ p64) ∨ (¬ p710) ∨ (¬ p904) ∨ p919 ∨ (¬ p1044) ∨ (¬ p1061) ∨ (¬ p1141) ∨ (¬ p1184)) : (¬ p6) ∨ (¬ p19) ∨ (¬ p64) ∨ (¬ p710) ∨ (¬ p904) ∨ (¬ p1044) ∨ (¬ p1061) ∨ (¬ p1141) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p919) := by
    exact h16230
  have u10 : p1184 := by
    exact h7053
  rcases h15792 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u9 q6)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u10)

theorem step20320 (p7 p15 p49 p84 p389 p456 p495 p789 p790 : Prop)
    (h16152 : (¬ p7))
    (h15793 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p789) ∨ (¬ p790)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p789) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15793 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20321 (p7 p15 p49 p84 p242 p616 p840 p906 p1061 p1115 : Prop)
    (h16152 : (¬ p7))
    (h15794 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p242) ∨ (¬ p616) ∨ (¬ p840) ∨ (¬ p906) ∨ (¬ p1061) ∨ (¬ p1115)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p242) ∨ (¬ p616) ∨ (¬ p840) ∨ (¬ p906) ∨ (¬ p1061) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p906 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15794 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20322 (p7 p185 p256 p426 p576 p792 p836 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h4535 : p792)
    (h15796 : p7 ∨ (¬ p185) ∨ (¬ p256) ∨ p426 ∨ (¬ p576) ∨ (¬ p792) ∨ (¬ p836)) : (¬ p185) ∨ (¬ p256) ∨ (¬ p576) ∨ (¬ p836) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p426) := by
    exact h16178
  have u6 : p792 := by
    exact h4535
  rcases h15796 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step20323 (p7 p125 p126 p141 p171 p237 p261 : Prop)
    (h16152 : (¬ p7))
    (h15797 : p7 ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p141) ∨ (¬ p171) ∨ (¬ p237) ∨ (¬ p261)) : (¬ p125) ∨ (¬ p126) ∨ (¬ p141) ∨ (¬ p171) ∨ (¬ p237) ∨ (¬ p261) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15797 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20324 (p7 p171 p187 p237 p303 p481 p521 p814 p996 : Prop)
    (h16152 : (¬ p7))
    (h15799 : p7 ∨ (¬ p171) ∨ (¬ p187) ∨ (¬ p237) ∨ (¬ p303) ∨ (¬ p481) ∨ (¬ p521) ∨ (¬ p814) ∨ (¬ p996)) : (¬ p171) ∨ (¬ p187) ∨ (¬ p237) ∨ (¬ p303) ∨ (¬ p481) ∨ (¬ p521) ∨ (¬ p814) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p521 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15799 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20326 (p7 p18 p127 p133 p234 p241 p382 p542 p657 p709 p792 p918 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h4535 : p792)
    (h15801 : p7 ∨ (¬ p18) ∨ (¬ p127) ∨ p133 ∨ (¬ p234) ∨ (¬ p241) ∨ (¬ p382) ∨ (¬ p542) ∨ (¬ p657) ∨ (¬ p709) ∨ (¬ p792) ∨ (¬ p918)) : (¬ p18) ∨ (¬ p127) ∨ (¬ p234) ∨ (¬ p241) ∨ (¬ p382) ∨ (¬ p542) ∨ (¬ p657) ∨ (¬ p709) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p133) := by
    exact h16157
  have u11 : p792 := by
    exact h4535
  rcases h15801 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u10 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u11)
  · exact False.elim (q11 u8)

theorem step20327 (p7 p142 p171 p237 p323 p347 p382 p657 p815 : Prop)
    (h16152 : (¬ p7))
    (h15802 : p7 ∨ (¬ p142) ∨ (¬ p171) ∨ (¬ p237) ∨ (¬ p323) ∨ (¬ p347) ∨ (¬ p382) ∨ (¬ p657) ∨ (¬ p815)) : (¬ p142) ∨ (¬ p171) ∨ (¬ p237) ∨ (¬ p323) ∨ (¬ p347) ∨ (¬ p382) ∨ (¬ p657) ∨ (¬ p815) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p815 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15802 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20328 (p7 p15 p19 p323 p347 p382 p621 p657 : Prop)
    (h16152 : (¬ p7))
    (h15803 : p7 ∨ (¬ p15) ∨ (¬ p19) ∨ (¬ p323) ∨ (¬ p347) ∨ (¬ p382) ∨ (¬ p621) ∨ (¬ p657)) : (¬ p15) ∨ (¬ p19) ∨ (¬ p323) ∨ (¬ p347) ∨ (¬ p382) ∨ (¬ p621) ∨ (¬ p657) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p621 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15803 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20329 (p7 p17 p107 p382 p480 p539 p752 p790 p1286 p1395 p1644 : Prop)
    (h16152 : (¬ p7))
    (h15804 : p7 ∨ (¬ p17) ∨ (¬ p107) ∨ (¬ p382) ∨ (¬ p480) ∨ (¬ p539) ∨ (¬ p752) ∨ (¬ p790) ∨ (¬ p1286) ∨ (¬ p1395) ∨ (¬ p1644)) : (¬ p17) ∨ (¬ p107) ∨ (¬ p382) ∨ (¬ p480) ∨ (¬ p539) ∨ (¬ p752) ∨ (¬ p790) ∨ (¬ p1286) ∨ (¬ p1395) ∨ (¬ p1644) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p480 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p539 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p752 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1395 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h15804 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)
  · exact False.elim (q10 u9)

theorem step20331 (p7 p237 p302 p792 p814 p858 p918 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h4535 : p792)
    (h15806 : p7 ∨ (¬ p237) ∨ p302 ∨ (¬ p792) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p918)) : (¬ p237) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p302) := by
    exact h16285
  have u6 : p792 := by
    exact h4535
  rcases h15806 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step20332 (p7 p18 p127 p133 p234 p685 p1366 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h3898 : p685)
    (h15807 : p7 ∨ (¬ p18) ∨ (¬ p127) ∨ p133 ∨ (¬ p234) ∨ (¬ p685) ∨ (¬ p1366)) : (¬ p18) ∨ (¬ p127) ∨ (¬ p234) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p133) := by
    exact h16157
  have u6 : p685 := by
    exact h3898
  rcases h15807 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step20333 (p7 p10 p102 p171 p187 p211 p224 p237 p302 p362 p814 p835 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h6478 : p1075)
    (h15809 : p7 ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p171) ∨ (¬ p187) ∨ (¬ p211) ∨ (¬ p224) ∨ (¬ p237) ∨ p302 ∨ (¬ p362) ∨ (¬ p814) ∨ (¬ p835) ∨ (¬ p1075)) : (¬ p10) ∨ (¬ p102) ∨ (¬ p171) ∨ (¬ p187) ∨ (¬ p211) ∨ (¬ p224) ∨ (¬ p237) ∨ (¬ p362) ∨ (¬ p814) ∨ (¬ p835) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p835 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : (¬ p302) := by
    exact h16285
  have u12 : p1075 := by
    exact h6478
  rcases h15809 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (u11 q8)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u8)
  · exact False.elim (q11 u9)
  · exact False.elim (q12 u12)

theorem step20334 (p7 p18 p72 p211 p227 p1206 : Prop)
    (h16152 : (¬ p7))
    (h15810 : p7 ∨ (¬ p18) ∨ (¬ p72) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p1206)) : (¬ p18) ∨ (¬ p72) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15810 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20335 (p7 p171 p187 p211 p227 p456 p575 p928 : Prop)
    (h16152 : (¬ p7))
    (h15812 : p7 ∨ (¬ p171) ∨ (¬ p187) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p456) ∨ (¬ p575) ∨ (¬ p928)) : (¬ p171) ∨ (¬ p187) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p456) ∨ (¬ p575) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p575 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15812 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20336 (p7 p224 p241 p302 p690 p709 p728 p792 p918 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h4535 : p792)
    (h15813 : p7 ∨ (¬ p224) ∨ (¬ p241) ∨ p302 ∨ (¬ p690) ∨ (¬ p709) ∨ (¬ p728) ∨ (¬ p792) ∨ (¬ p918)) : (¬ p224) ∨ (¬ p241) ∨ (¬ p690) ∨ (¬ p709) ∨ (¬ p728) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p302) := by
    exact h16285
  have u8 : p792 := by
    exact h4535
  rcases h15813 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u7 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u5)

theorem step20337 (p7 p18 p127 p133 p224 p241 p423 p710 p792 p918 p1000 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h4535 : p792)
    (h15814 : p7 ∨ (¬ p18) ∨ (¬ p127) ∨ p133 ∨ (¬ p224) ∨ (¬ p241) ∨ (¬ p423) ∨ (¬ p710) ∨ (¬ p792) ∨ (¬ p918) ∨ (¬ p1000)) : (¬ p18) ∨ (¬ p127) ∨ (¬ p224) ∨ (¬ p241) ∨ (¬ p423) ∨ (¬ p710) ∨ (¬ p918) ∨ (¬ p1000) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p133) := by
    exact h16157
  have u10 : p792 := by
    exact h4535
  rcases h15814 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u9 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step20338 (p7 p241 p455 p499 p710 p734 p792 p918 p1136 p1335 p1452 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16259 : (¬ p1136))
    (h15815 : p7 ∨ (¬ p241) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p710) ∨ (¬ p734) ∨ (¬ p792) ∨ (¬ p918) ∨ p1136 ∨ (¬ p1335) ∨ (¬ p1452)) : (¬ p241) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p710) ∨ (¬ p734) ∨ (¬ p918) ∨ (¬ p1335) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p792 := by
    exact h4535
  have u10 : (¬ p1136) := by
    exact h16259
  rcases h15815 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u5)
  · exact False.elim (u10 q8)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step20339 (p7 p41 p121 p127 p187 p230 p710 p904 p1074 p1081 p1097 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h7053 : p1184)
    (h15816 : p7 ∨ (¬ p41) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p187) ∨ p230 ∨ (¬ p710) ∨ (¬ p904) ∨ (¬ p1074) ∨ (¬ p1081) ∨ (¬ p1097) ∨ (¬ p1184)) : (¬ p41) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p187) ∨ (¬ p710) ∨ (¬ p904) ∨ (¬ p1074) ∨ (¬ p1081) ∨ (¬ p1097) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1097 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p230) := by
    exact h16165
  have u11 : p1184 := by
    exact h7053
  rcases h15816 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u10 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u8)
  · exact False.elim (q11 u11)

theorem step20340 (p7 p230 p323 p427 p581 p1206 p1443 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h2334 : p427)
    (h15817 : p7 ∨ p230 ∨ (¬ p323) ∨ (¬ p427) ∨ (¬ p581) ∨ (¬ p1206) ∨ (¬ p1443)) : (¬ p323) ∨ (¬ p581) ∨ (¬ p1206) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p427 := by
    exact h2334
  rcases h15817 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step20341 (p7 p237 p537 p738 p814 p835 : Prop)
    (h16152 : (¬ p7))
    (h15818 : p7 ∨ (¬ p237) ∨ (¬ p537) ∨ (¬ p738) ∨ (¬ p814) ∨ (¬ p835)) : (¬ p237) ∨ (¬ p537) ∨ (¬ p738) ∨ (¬ p814) ∨ (¬ p835) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p738 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p835 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15818 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20342 (p7 p10 p121 p362 p496 p1074 p1081 p1099 : Prop)
    (h16152 : (¬ p7))
    (h15819 : p7 ∨ (¬ p10) ∨ (¬ p121) ∨ (¬ p362) ∨ (¬ p496) ∨ (¬ p1074) ∨ (¬ p1081) ∨ (¬ p1099)) : (¬ p10) ∨ (¬ p121) ∨ (¬ p362) ∨ (¬ p496) ∨ (¬ p1074) ∨ (¬ p1081) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15819 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20343 (p7 p70 p481 p985 p996 p1099 p1333 p1538 : Prop)
    (h16152 : (¬ p7))
    (h15820 : p7 ∨ (¬ p70) ∨ (¬ p481) ∨ (¬ p985) ∨ (¬ p996) ∨ (¬ p1099) ∨ (¬ p1333) ∨ (¬ p1538)) : (¬ p70) ∨ (¬ p481) ∨ (¬ p985) ∨ (¬ p996) ∨ (¬ p1099) ∨ (¬ p1333) ∨ (¬ p1538) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15820 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20345 (p7 p15 p234 p237 p792 p864 p918 p996 p1136 p1349 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16259 : (¬ p1136))
    (h15822 : p7 ∨ (¬ p15) ∨ (¬ p234) ∨ (¬ p237) ∨ (¬ p792) ∨ (¬ p864) ∨ (¬ p918) ∨ (¬ p996) ∨ p1136 ∨ (¬ p1349)) : (¬ p15) ∨ (¬ p234) ∨ (¬ p237) ∨ (¬ p864) ∨ (¬ p918) ∨ (¬ p996) ∨ (¬ p1349) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p792 := by
    exact h4535
  have u9 : (¬ p1136) := by
    exact h16259
  rcases h15822 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u9 q8)
  · exact False.elim (q9 u6)

theorem step20346 (p7 p171 p187 p211 p362 p420 p575 p928 : Prop)
    (h16152 : (¬ p7))
    (h15823 : p7 ∨ (¬ p171) ∨ (¬ p187) ∨ (¬ p211) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p575) ∨ (¬ p928)) : (¬ p171) ∨ (¬ p187) ∨ (¬ p211) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p575) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p575 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15823 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20347 (p7 p237 p669 p792 p918 p1118 p1136 p1225 p1229 p1325 p1349 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16259 : (¬ p1136))
    (h15824 : p7 ∨ (¬ p237) ∨ (¬ p669) ∨ (¬ p792) ∨ (¬ p918) ∨ (¬ p1118) ∨ p1136 ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1325) ∨ (¬ p1349)) : (¬ p237) ∨ (¬ p669) ∨ (¬ p918) ∨ (¬ p1118) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1325) ∨ (¬ p1349) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1118 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p792 := by
    exact h4535
  have u10 : (¬ p1136) := by
    exact h16259
  rcases h15824 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u10 q6)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step20348 (p7 p241 p362 p420 p455 p658 p792 p918 p983 p1056 p1081 p1226 : Prop)
    (h16152 : (¬ p7))
    (h16199 : (¬ p658))
    (h4535 : p792)
    (h15825 : p7 ∨ (¬ p241) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p455) ∨ p658 ∨ (¬ p792) ∨ (¬ p918) ∨ (¬ p983) ∨ (¬ p1056) ∨ (¬ p1081) ∨ (¬ p1226)) : (¬ p241) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p455) ∨ (¬ p918) ∨ (¬ p983) ∨ (¬ p1056) ∨ (¬ p1081) ∨ (¬ p1226) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1056 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p658) := by
    exact h16199
  have u11 : p792 := by
    exact h4535
  rcases h15825 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u10 q5)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step20349 (p7 p15 p234 p241 p792 p918 p980 p1055 p1136 p1330 p1366 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16259 : (¬ p1136))
    (h15826 : p7 ∨ (¬ p15) ∨ (¬ p234) ∨ (¬ p241) ∨ (¬ p792) ∨ (¬ p918) ∨ (¬ p980) ∨ (¬ p1055) ∨ p1136 ∨ (¬ p1330) ∨ (¬ p1366)) : (¬ p15) ∨ (¬ p234) ∨ (¬ p241) ∨ (¬ p918) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1330) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p792 := by
    exact h4535
  have u10 : (¬ p1136) := by
    exact h16259
  rcases h15826 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u10 q8)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step20350 (p7 p42 p125 p160 p161 p167 p236 p280 p883 p1306 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16173 : (¬ p280))
    (h15827 : p7 ∨ (¬ p42) ∨ (¬ p125) ∨ (¬ p160) ∨ (¬ p161) ∨ (¬ p167) ∨ (¬ p236) ∨ p280 ∨ (¬ p883) ∨ (¬ p1306)) : (¬ p125) ∨ (¬ p160) ∨ (¬ p161) ∨ (¬ p167) ∨ (¬ p236) ∨ (¬ p883) ∨ (¬ p1306) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p236 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p42 := by
    exact h132
  have u9 : (¬ p280) := by
    exact h16173
  rcases h15827 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u9 q7)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step20351 (p5 p6 p7 p10 p63 p302 p303 p343 p840 p928 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h1950 : p343)
    (h15828 : (¬ p5) ∨ (¬ p6) ∨ p7 ∨ (¬ p10) ∨ (¬ p63) ∨ p302 ∨ (¬ p303) ∨ (¬ p343) ∨ (¬ p840) ∨ (¬ p928)) : (¬ p5) ∨ (¬ p6) ∨ (¬ p10) ∨ (¬ p63) ∨ (¬ p303) ∨ (¬ p840) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p302) := by
    exact h16285
  have u9 : p343 := by
    exact h1950
  rcases h15828 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u8 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step20352 (p5 p6 p7 p10 p41 p42 p89 p237 p302 p303 p918 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16285 : (¬ p302))
    (h15829 : (¬ p5) ∨ (¬ p6) ∨ p7 ∨ (¬ p10) ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p89) ∨ (¬ p237) ∨ p302 ∨ (¬ p303) ∨ (¬ p918)) : (¬ p5) ∨ (¬ p6) ∨ (¬ p10) ∨ (¬ p41) ∨ (¬ p89) ∨ (¬ p237) ∨ (¬ p303) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p42 := by
    exact h132
  have u10 : (¬ p302) := by
    exact h16285
  rcases h15829 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u8 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u10 q8)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step20353 (p132 p135 p193 p791 : Prop)
    (h786 : p132)
    (h16213 : (¬ p791))
    (h15830 : (¬ p132) ∨ p135 ∨ (¬ p193) ∨ p791) : p135 ∨ (¬ p193) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p135) := fun hu => hn (Or.inl hu)
  have u1 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p132 := by
    exact h786
  have u3 : (¬ p791) := by
    exact h16213
  rcases h15830 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u3 q3)

theorem step20355 (p7 p89 p237 p382 p387 p517 p621 p856 p918 p1273 : Prop)
    (h16152 : (¬ p7))
    (h15832 : p7 ∨ (¬ p89) ∨ (¬ p237) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p517) ∨ (¬ p621) ∨ (¬ p856) ∨ (¬ p918) ∨ (¬ p1273)) : (¬ p89) ∨ (¬ p237) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p517) ∨ (¬ p621) ∨ (¬ p856) ∨ (¬ p918) ∨ (¬ p1273) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p517 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p621 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p856 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15832 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20356 (p7 p128 p302 p303 p434 p435 p1187 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16285 : (¬ p302))
    (h15833 : p7 ∨ (¬ p128) ∨ p302 ∨ (¬ p303) ∨ (¬ p434) ∨ (¬ p435) ∨ (¬ p1187)) : (¬ p303) ∨ (¬ p434) ∨ (¬ p435) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p128 := by
    exact h653
  have u6 : (¬ p302) := by
    exact h16285
  rcases h15833 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step20357 (p7 p42 p134 p210 p304 p980 p1076 p1324 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16309 : (¬ p1324))
    (h15834 : p7 ∨ (¬ p42) ∨ (¬ p134) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p980) ∨ (¬ p1076) ∨ p1324) : (¬ p134) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p980) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p1324) := by
    exact h16309
  rcases h15834 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step20359 (p6 p7 p10 p188 p239 p438 p983 p1061 p1335 : Prop)
    (h16152 : (¬ p7))
    (h15836 : (¬ p6) ∨ p7 ∨ (¬ p10) ∨ (¬ p188) ∨ (¬ p239) ∨ (¬ p438) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1335)) : (¬ p6) ∨ (¬ p10) ∨ (¬ p188) ∨ (¬ p239) ∨ (¬ p438) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1335) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p239 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15836 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20360 (p7 p306 p350 p601 p634 p1061 p1074 : Prop)
    (h16152 : (¬ p7))
    (h15837 : p7 ∨ (¬ p306) ∨ (¬ p350) ∨ (¬ p601) ∨ (¬ p634) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p306) ∨ (¬ p350) ∨ (¬ p601) ∨ (¬ p634) ∨ (¬ p1061) ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p634 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15837 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20361 (p7 p306 p350 p536 p601 p634 p1538 : Prop)
    (h16152 : (¬ p7))
    (h15838 : p7 ∨ (¬ p306) ∨ (¬ p350) ∨ (¬ p536) ∨ (¬ p601) ∨ (¬ p634) ∨ (¬ p1538)) : (¬ p306) ∨ (¬ p350) ∨ (¬ p536) ∨ (¬ p601) ∨ (¬ p634) ∨ (¬ p1538) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p634 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15838 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20363 (p7 p638 p983 p1056 p1077 p1102 p1226 : Prop)
    (h16152 : (¬ p7))
    (h15840 : p7 ∨ (¬ p638) ∨ (¬ p983) ∨ (¬ p1056) ∨ (¬ p1077) ∨ (¬ p1102) ∨ (¬ p1226)) : (¬ p638) ∨ (¬ p983) ∨ (¬ p1056) ∨ (¬ p1077) ∨ (¬ p1102) ∨ (¬ p1226) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p638 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1056 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15840 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20364 (p6 p7 p142 p165 p659 p686 p1077 p1115 : Prop)
    (h16152 : (¬ p7))
    (h3753 : p659)
    (h16205 : (¬ p686))
    (h15842 : (¬ p6) ∨ p7 ∨ (¬ p142) ∨ (¬ p165) ∨ (¬ p659) ∨ p686 ∨ (¬ p1077) ∨ (¬ p1115)) : (¬ p6) ∨ (¬ p142) ∨ (¬ p165) ∨ (¬ p1077) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p165 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p659 := by
    exact h3753
  have u7 : (¬ p686) := by
    exact h16205
  rcases h15842 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (u7 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step20365 (p7 p160 p161 p925 p1057 p1116 p1306 : Prop)
    (h16152 : (¬ p7))
    (h15843 : p7 ∨ (¬ p160) ∨ (¬ p161) ∨ (¬ p925) ∨ (¬ p1057) ∨ (¬ p1116) ∨ (¬ p1306)) : (¬ p160) ∨ (¬ p161) ∨ (¬ p925) ∨ (¬ p1057) ∨ (¬ p1116) ∨ (¬ p1306) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p925 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1057 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15843 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20366 (p7 p422 p424 p1366 p1484 p1545 p1664 : Prop)
    (h16152 : (¬ p7))
    (h16345 : (¬ p1484))
    (h10244 : p1664)
    (h15844 : p7 ∨ (¬ p422) ∨ (¬ p424) ∨ (¬ p1366) ∨ p1484 ∨ (¬ p1545) ∨ (¬ p1664)) : (¬ p422) ∨ (¬ p424) ∨ (¬ p1366) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p1484) := by
    exact h16345
  have u6 : p1664 := by
    exact h10244
  rcases h15844 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step20367 (p2 p7 p160 p188 p422 p424 p980 p1044 p1350 : Prop)
    (h16152 : (¬ p7))
    (h15845 : (¬ p2) ∨ p7 ∨ (¬ p160) ∨ (¬ p188) ∨ (¬ p422) ∨ (¬ p424) ∨ (¬ p980) ∨ (¬ p1044) ∨ (¬ p1350)) : (¬ p2) ∨ (¬ p160) ∨ (¬ p188) ∨ (¬ p422) ∨ (¬ p424) ∨ (¬ p980) ∨ (¬ p1044) ∨ (¬ p1350) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15845 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20368 (p6 p7 p10 p88 p188 p303 p665 p924 p1099 p1229 p1310 : Prop)
    (h16152 : (¬ p7))
    (h15846 : (¬ p6) ∨ p7 ∨ (¬ p10) ∨ (¬ p88) ∨ (¬ p188) ∨ (¬ p303) ∨ (¬ p665) ∨ (¬ p924) ∨ (¬ p1099) ∨ (¬ p1229) ∨ (¬ p1310)) : (¬ p6) ∨ (¬ p10) ∨ (¬ p88) ∨ (¬ p188) ∨ (¬ p303) ∨ (¬ p665) ∨ (¬ p924) ∨ (¬ p1099) ∨ (¬ p1229) ∨ (¬ p1310) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h15846 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u0)
  · exact False.elim (u10 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)
  · exact False.elim (q10 u9)

theorem step20370 (p7 p41 p127 p137 p195 p576 : Prop)
    (h16152 : (¬ p7))
    (h15848 : p7 ∨ (¬ p41) ∨ (¬ p127) ∨ (¬ p137) ∨ (¬ p195) ∨ (¬ p576)) : (¬ p41) ∨ (¬ p127) ∨ (¬ p137) ∨ (¬ p195) ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p137 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15848 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20371 (p2 p7 p45 p192 p280 p387 p419 p792 : Prop)
    (h16152 : (¬ p7))
    (h16173 : (¬ p280))
    (h4535 : p792)
    (h15849 : (¬ p2) ∨ p7 ∨ (¬ p45) ∨ (¬ p192) ∨ p280 ∨ (¬ p387) ∨ (¬ p419) ∨ (¬ p792)) : (¬ p2) ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p387) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p280) := by
    exact h16173
  have u7 : p792 := by
    exact h4535
  rcases h15849 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step20372 (p7 p101 p125 p265 p323 p576 p686 p792 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h4535 : p792)
    (h15850 : p7 ∨ (¬ p101) ∨ (¬ p125) ∨ (¬ p265) ∨ (¬ p323) ∨ (¬ p576) ∨ p686 ∨ (¬ p792)) : (¬ p101) ∨ (¬ p125) ∨ (¬ p265) ∨ (¬ p323) ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p686) := by
    exact h16205
  have u7 : p792 := by
    exact h4535
  rcases h15850 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u7)

theorem step20373 (p6 p7 p45 p90 p101 p126 p192 p256 p350 : Prop)
    (h16152 : (¬ p7))
    (h15851 : (¬ p6) ∨ p7 ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p101) ∨ (¬ p126) ∨ (¬ p192) ∨ (¬ p256) ∨ (¬ p350)) : (¬ p6) ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p101) ∨ (¬ p126) ∨ (¬ p192) ∨ (¬ p256) ∨ (¬ p350) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15851 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20374 (p7 p85 p595 p929 p980 p1074 p1330 p1542 : Prop)
    (h16152 : (¬ p7))
    (h15852 : p7 ∨ (¬ p85) ∨ (¬ p595) ∨ (¬ p929) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1330) ∨ (¬ p1542)) : (¬ p85) ∨ (¬ p595) ∨ (¬ p929) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1330) ∨ (¬ p1542) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p929 := by
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
  have u5 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15852 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20375 (p7 p42 p167 p560 p769 p1074 p1181 p1562 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16272 : (¬ p1181))
    (h15853 : p7 ∨ (¬ p42) ∨ (¬ p167) ∨ (¬ p560) ∨ (¬ p769) ∨ (¬ p1074) ∨ p1181 ∨ (¬ p1562)) : (¬ p167) ∨ (¬ p560) ∨ (¬ p769) ∨ (¬ p1074) ∨ (¬ p1562) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p1181) := by
    exact h16272
  rcases h15853 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step20376 (p7 p86 p161 p256 p983 p1081 p1232 p1443 : Prop)
    (h16152 : (¬ p7))
    (h15854 : p7 ∨ (¬ p86) ∨ (¬ p161) ∨ (¬ p256) ∨ (¬ p983) ∨ (¬ p1081) ∨ (¬ p1232) ∨ (¬ p1443)) : (¬ p86) ∨ (¬ p161) ∨ (¬ p256) ∨ (¬ p983) ∨ (¬ p1081) ∨ (¬ p1232) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15854 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20377 (p7 p40 p69 p1135 p1225 p1229 p1325 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h6744 : p1135)
    (h15855 : p7 ∨ p40 ∨ (¬ p69) ∨ (¬ p1135) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1325)) : (¬ p69) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p40) := by
    exact h16150
  have u6 : p1135 := by
    exact h6744
  rcases h15855 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step20378 (p2 p4 p7 p12 p14 p38 p325 p668 : Prop)
    (h16152 : (¬ p7))
    (h15856 : (¬ p2) ∨ (¬ p4) ∨ p7 ∨ (¬ p12) ∨ (¬ p14) ∨ (¬ p38) ∨ (¬ p325) ∨ (¬ p668)) : (¬ p2) ∨ (¬ p4) ∨ (¬ p12) ∨ (¬ p14) ∨ (¬ p38) ∨ (¬ p325) ∨ (¬ p668) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15856 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20379 (p7 p19 p42 p68 p134 p225 p226 p426 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16178 : (¬ p426))
    (h15857 : p7 ∨ (¬ p19) ∨ (¬ p42) ∨ p68 ∨ (¬ p134) ∨ (¬ p225) ∨ (¬ p226) ∨ p426) : (¬ p19) ∨ p68 ∨ (¬ p134) ∨ (¬ p225) ∨ (¬ p226) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p68) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p426) := by
    exact h16178
  rcases h15857 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step20380 (p7 p45 p90 p192 p225 p226 p237 p668 p923 p1095 : Prop)
    (h16152 : (¬ p7))
    (h15858 : p7 ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p192) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p237) ∨ (¬ p668) ∨ (¬ p923) ∨ (¬ p1095)) : (¬ p45) ∨ (¬ p90) ∨ (¬ p192) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p237) ∨ (¬ p668) ∨ (¬ p923) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p90 := by
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
  have u4 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p923 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15858 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20381 (p7 p63 p389 p789 p1226 p1237 p1393 p1452 : Prop)
    (h16152 : (¬ p7))
    (h15859 : p7 ∨ (¬ p63) ∨ (¬ p389) ∨ (¬ p789) ∨ (¬ p1226) ∨ (¬ p1237) ∨ (¬ p1393) ∨ (¬ p1452)) : (¬ p63) ∨ (¬ p389) ∨ (¬ p789) ∨ (¬ p1226) ∨ (¬ p1237) ∨ (¬ p1393) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15859 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20382 (p7 p500 p532 p595 p669 p961 p983 p1286 : Prop)
    (h16152 : (¬ p7))
    (h15860 : p7 ∨ (¬ p500) ∨ (¬ p532) ∨ (¬ p595) ∨ (¬ p669) ∨ (¬ p961) ∨ (¬ p983) ∨ (¬ p1286)) : (¬ p500) ∨ (¬ p532) ∨ (¬ p595) ∨ (¬ p669) ∨ (¬ p961) ∨ (¬ p983) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15860 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20383 (p7 p19 p42 p48 p134 p790 p791 p1385 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16213 : (¬ p791))
    (h15861 : p7 ∨ (¬ p19) ∨ (¬ p42) ∨ (¬ p48) ∨ (¬ p134) ∨ (¬ p790) ∨ p791 ∨ (¬ p1385)) : (¬ p19) ∨ (¬ p48) ∨ (¬ p134) ∨ (¬ p790) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p791) := by
    exact h16213
  rcases h15861 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step20384 (p7 p42 p63 p134 p210 p304 p726 p985 p1136 p1273 p1508 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16259 : (¬ p1136))
    (h15862 : p7 ∨ (¬ p42) ∨ (¬ p63) ∨ (¬ p134) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p726) ∨ (¬ p985) ∨ p1136 ∨ (¬ p1273) ∨ (¬ p1508)) : (¬ p63) ∨ (¬ p134) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p726) ∨ (¬ p985) ∨ (¬ p1273) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p42 := by
    exact h132
  have u10 : (¬ p1136) := by
    exact h16259
  rcases h15862 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u10 q8)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step20385 (p7 p142 p326 p797 p858 p996 : Prop)
    (h16152 : (¬ p7))
    (h15863 : p7 ∨ (¬ p142) ∨ (¬ p326) ∨ (¬ p797) ∨ (¬ p858) ∨ (¬ p996)) : (¬ p142) ∨ (¬ p326) ∨ (¬ p797) ∨ (¬ p858) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p797 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15863 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20386 (p7 p41 p142 p788 p790 p791 p1385 : Prop)
    (h16152 : (¬ p7))
    (h5066 : p788)
    (h16213 : (¬ p791))
    (h15864 : p7 ∨ (¬ p41) ∨ (¬ p142) ∨ (¬ p788) ∨ (¬ p790) ∨ p791 ∨ (¬ p1385)) : (¬ p41) ∨ (¬ p142) ∨ (¬ p790) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p788 := by
    exact h5066
  have u6 : (¬ p791) := by
    exact h16213
  rcases h15864 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step20387 (p2 p3 p7 p19 p229 p326 : Prop)
    (h16152 : (¬ p7))
    (h15865 : (¬ p2) ∨ (¬ p3) ∨ p7 ∨ (¬ p19) ∨ (¬ p229) ∨ (¬ p326)) : (¬ p2) ∨ (¬ p3) ∨ (¬ p19) ∨ (¬ p229) ∨ (¬ p326) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15865 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20388 (p7 p19 p225 p426 p557 p788 p879 p1061 p1074 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h5066 : p788)
    (h15866 : p7 ∨ (¬ p19) ∨ (¬ p225) ∨ p426 ∨ (¬ p557) ∨ (¬ p788) ∨ (¬ p879) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p19) ∨ (¬ p225) ∨ (¬ p557) ∨ (¬ p879) ∨ (¬ p1061) ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p879 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p426) := by
    exact h16178
  have u8 : p788 := by
    exact h5066
  rcases h15866 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u7 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step20390 (p7 p90 p265 p304 p576 p669 p789 p790 p1076 : Prop)
    (h16152 : (¬ p7))
    (h15869 : p7 ∨ (¬ p90) ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p576) ∨ (¬ p669) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1076)) : (¬ p90) ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p576) ∨ (¬ p669) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15869 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20391 (p7 p90 p106 p163 p193 p265 p305 p576 p1055 p1077 : Prop)
    (h16152 : (¬ p7))
    (h15870 : p7 ∨ (¬ p90) ∨ (¬ p106) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p265) ∨ (¬ p305) ∨ (¬ p576) ∨ (¬ p1055) ∨ (¬ p1077)) : (¬ p90) ∨ (¬ p106) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p265) ∨ (¬ p305) ∨ (¬ p576) ∨ (¬ p1055) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15870 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20392 (p7 p63 p304 p500 p669 p789 p1076 p1393 : Prop)
    (h16152 : (¬ p7))
    (h15871 : p7 ∨ (¬ p63) ∨ (¬ p304) ∨ (¬ p500) ∨ (¬ p669) ∨ (¬ p789) ∨ (¬ p1076) ∨ (¬ p1393)) : (¬ p63) ∨ (¬ p304) ∨ (¬ p500) ∨ (¬ p669) ∨ (¬ p789) ∨ (¬ p1076) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15871 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20394 (p7 p19 p229 p686 p788 p1036 p1077 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h5066 : p788)
    (h15873 : p7 ∨ (¬ p19) ∨ (¬ p229) ∨ p686 ∨ (¬ p788) ∨ (¬ p1036) ∨ (¬ p1077)) : (¬ p19) ∨ (¬ p229) ∨ (¬ p1036) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p686) := by
    exact h16205
  have u6 : p788 := by
    exact h5066
  rcases h15873 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step20395 (p7 p25 p71 p101 p481 p633 p788 p1136 p1187 : Prop)
    (h16152 : (¬ p7))
    (h5066 : p788)
    (h16259 : (¬ p1136))
    (h15874 : p7 ∨ (¬ p25) ∨ (¬ p71) ∨ (¬ p101) ∨ (¬ p481) ∨ (¬ p633) ∨ (¬ p788) ∨ p1136 ∨ (¬ p1187)) : (¬ p25) ∨ (¬ p71) ∨ (¬ p101) ∨ (¬ p481) ∨ (¬ p633) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p25 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : p788 := by
    exact h5066
  have u8 : (¬ p1136) := by
    exact h16259
  rcases h15874 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u7)
  · exact False.elim (u8 q7)
  · exact False.elim (q8 u5)

theorem step20396 (p7 p19 p280 p434 p435 p788 p1187 : Prop)
    (h16152 : (¬ p7))
    (h16173 : (¬ p280))
    (h5066 : p788)
    (h15875 : p7 ∨ (¬ p19) ∨ p280 ∨ (¬ p434) ∨ (¬ p435) ∨ (¬ p788) ∨ (¬ p1187)) : (¬ p19) ∨ (¬ p434) ∨ (¬ p435) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p280) := by
    exact h16173
  have u6 : p788 := by
    exact h5066
  rcases h15875 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step20397 (p7 p15 p142 p234 p788 p796 p1136 : Prop)
    (h16152 : (¬ p7))
    (h5066 : p788)
    (h16259 : (¬ p1136))
    (h15876 : p7 ∨ (¬ p15) ∨ (¬ p142) ∨ (¬ p234) ∨ (¬ p788) ∨ (¬ p796) ∨ p1136) : (¬ p15) ∨ (¬ p142) ∨ (¬ p234) ∨ (¬ p796) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p788 := by
    exact h5066
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h15876 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step20398 (p7 p45 p193 p789 p791 p1135 p1393 : Prop)
    (h16152 : (¬ p7))
    (h16213 : (¬ p791))
    (h6744 : p1135)
    (h15877 : p7 ∨ (¬ p45) ∨ (¬ p193) ∨ (¬ p789) ∨ p791 ∨ (¬ p1135) ∨ (¬ p1393)) : (¬ p45) ∨ (¬ p193) ∨ (¬ p789) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p791) := by
    exact h16213
  have u6 : p1135 := by
    exact h6744
  rcases h15877 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step20399 (p7 p45 p89 p193 p285 p928 p1055 p1077 p1103 : Prop)
    (h16152 : (¬ p7))
    (h15878 : p7 ∨ (¬ p45) ∨ (¬ p89) ∨ (¬ p193) ∨ (¬ p285) ∨ (¬ p928) ∨ (¬ p1055) ∨ (¬ p1077) ∨ (¬ p1103)) : (¬ p45) ∨ (¬ p89) ∨ (¬ p193) ∨ (¬ p285) ∨ (¬ p928) ∨ (¬ p1055) ∨ (¬ p1077) ∨ (¬ p1103) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p285 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15878 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20400 (p7 p44 p90 p193 p234 p241 p669 p918 p996 p1055 : Prop)
    (h16152 : (¬ p7))
    (h15879 : p7 ∨ (¬ p44) ∨ (¬ p90) ∨ (¬ p193) ∨ (¬ p234) ∨ (¬ p241) ∨ (¬ p669) ∨ (¬ p918) ∨ (¬ p996) ∨ (¬ p1055)) : (¬ p44) ∨ (¬ p90) ∨ (¬ p193) ∨ (¬ p234) ∨ (¬ p241) ∨ (¬ p669) ∨ (¬ p918) ∨ (¬ p996) ∨ (¬ p1055) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15879 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20401 (p7 p15 p423 p1035 p1135 p1136 p1325 : Prop)
    (h16152 : (¬ p7))
    (h6744 : p1135)
    (h16259 : (¬ p1136))
    (h15880 : p7 ∨ (¬ p15) ∨ (¬ p423) ∨ (¬ p1035) ∨ (¬ p1135) ∨ p1136 ∨ (¬ p1325)) : (¬ p15) ∨ (¬ p423) ∨ (¬ p1035) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p1135 := by
    exact h6744
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h15880 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step20402 (p7 p45 p124 p193 p636 p791 p961 p1273 p1490 p1530 : Prop)
    (h16152 : (¬ p7))
    (h16213 : (¬ p791))
    (h9352 : p1530)
    (h15881 : p7 ∨ (¬ p45) ∨ (¬ p124) ∨ (¬ p193) ∨ (¬ p636) ∨ p791 ∨ (¬ p961) ∨ (¬ p1273) ∨ (¬ p1490) ∨ (¬ p1530)) : (¬ p45) ∨ (¬ p124) ∨ (¬ p193) ∨ (¬ p636) ∨ (¬ p961) ∨ (¬ p1273) ∨ (¬ p1490) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1490 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p791) := by
    exact h16213
  have u9 : p1530 := by
    exact h9352
  rcases h15881 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u8 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u9)

theorem step20403 (p7 p132 p280 p434 p581 p1015 p1385 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16173 : (¬ p280))
    (h15882 : p7 ∨ (¬ p132) ∨ p280 ∨ (¬ p434) ∨ (¬ p581) ∨ (¬ p1015) ∨ (¬ p1385)) : (¬ p434) ∨ (¬ p581) ∨ (¬ p1015) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p132 := by
    exact h786
  have u6 : (¬ p280) := by
    exact h16173
  rcases h15882 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step20404 (p7 p124 p125 p132 p258 p430 p438 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16180 : (¬ p430))
    (h15883 : p7 ∨ (¬ p124) ∨ (¬ p125) ∨ (¬ p132) ∨ (¬ p258) ∨ p430 ∨ (¬ p438)) : (¬ p124) ∨ (¬ p125) ∨ (¬ p258) ∨ (¬ p438) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p132 := by
    exact h786
  have u6 : (¬ p430) := by
    exact h16180
  rcases h15883 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step20405 (p7 p15 p234 p309 p636 p980 p1055 p1136 p1330 p1366 p1530 : Prop)
    (h16152 : (¬ p7))
    (h16259 : (¬ p1136))
    (h9352 : p1530)
    (h15884 : p7 ∨ (¬ p15) ∨ (¬ p234) ∨ (¬ p309) ∨ (¬ p636) ∨ (¬ p980) ∨ (¬ p1055) ∨ p1136 ∨ (¬ p1330) ∨ (¬ p1366) ∨ (¬ p1530)) : (¬ p15) ∨ (¬ p234) ∨ (¬ p309) ∨ (¬ p636) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1330) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p1136) := by
    exact h16259
  have u10 : p1530 := by
    exact h9352
  rcases h15884 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u9 q7)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u10)

theorem step20406 (p7 p15 p234 p304 p500 p669 p996 p1076 : Prop)
    (h16152 : (¬ p7))
    (h15885 : p7 ∨ (¬ p15) ∨ (¬ p234) ∨ (¬ p304) ∨ (¬ p500) ∨ (¬ p669) ∨ (¬ p996) ∨ (¬ p1076)) : (¬ p15) ∨ (¬ p234) ∨ (¬ p304) ∨ (¬ p500) ∨ (¬ p669) ∨ (¬ p996) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15885 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20407 (p7 p15 p224 p234 p343 p996 p1136 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16259 : (¬ p1136))
    (h15886 : p7 ∨ (¬ p15) ∨ (¬ p224) ∨ (¬ p234) ∨ (¬ p343) ∨ (¬ p996) ∨ p1136) : (¬ p15) ∨ (¬ p224) ∨ (¬ p234) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p343 := by
    exact h1950
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h15886 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step20408 (p7 p101 p124 p125 p430 p438 p788 : Prop)
    (h16152 : (¬ p7))
    (h16180 : (¬ p430))
    (h5066 : p788)
    (h15887 : p7 ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p125) ∨ p430 ∨ (¬ p438) ∨ (¬ p788)) : (¬ p101) ∨ (¬ p124) ∨ (¬ p125) ∨ (¬ p438) := by
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
  have u2 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p430) := by
    exact h16180
  have u6 : p788 := by
    exact h5066
  rcases h15887 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step20409 (p7 p14 p164 p983 p1141 p1167 p1181 p1226 : Prop)
    (h16152 : (¬ p7))
    (h789 : p164)
    (h16272 : (¬ p1181))
    (h15888 : p7 ∨ (¬ p14) ∨ (¬ p164) ∨ (¬ p983) ∨ (¬ p1141) ∨ (¬ p1167) ∨ p1181 ∨ (¬ p1226)) : (¬ p14) ∨ (¬ p983) ∨ (¬ p1141) ∨ (¬ p1167) ∨ (¬ p1226) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p164 := by
    exact h789
  have u7 : (¬ p1181) := by
    exact h16272
  rcases h15888 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step20410 (p7 p19 p134 p195 p481 p1187 : Prop)
    (h16152 : (¬ p7))
    (h15889 : p7 ∨ (¬ p19) ∨ (¬ p134) ∨ (¬ p195) ∨ (¬ p481) ∨ (¬ p1187)) : (¬ p19) ∨ (¬ p134) ∨ (¬ p195) ∨ (¬ p481) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15889 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20411 (p3 p7 p12 p24 p134 p195 p304 p346 p425 p668 : Prop)
    (h16152 : (¬ p7))
    (h15890 : (¬ p3) ∨ p7 ∨ (¬ p12) ∨ (¬ p24) ∨ (¬ p134) ∨ (¬ p195) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p425) ∨ (¬ p668)) : (¬ p3) ∨ (¬ p12) ∨ (¬ p24) ∨ (¬ p134) ∨ (¬ p195) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p425) ∨ (¬ p668) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15890 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (u9 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20412 (p7 p42 p167 p346 p426 p1036 p1077 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16178 : (¬ p426))
    (h15891 : p7 ∨ (¬ p42) ∨ (¬ p167) ∨ (¬ p346) ∨ p426 ∨ (¬ p1036) ∨ (¬ p1077)) : (¬ p167) ∨ (¬ p346) ∨ (¬ p1036) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p42 := by
    exact h132
  have u6 : (¬ p426) := by
    exact h16178
  rcases h15891 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step20413 (p7 p24 p42 p63 p125 p134 p425 p431 p438 p789 p1136 p1393 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16259 : (¬ p1136))
    (h15892 : p7 ∨ (¬ p24) ∨ (¬ p42) ∨ (¬ p63) ∨ (¬ p125) ∨ (¬ p134) ∨ (¬ p425) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p789) ∨ p1136 ∨ (¬ p1393)) : (¬ p24) ∨ (¬ p63) ∨ (¬ p125) ∨ (¬ p134) ∨ (¬ p425) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p789) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p42 := by
    exact h132
  have u11 : (¬ p1136) := by
    exact h16259
  rcases h15892 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (u11 q10)
  · exact False.elim (q11 u8)

theorem step20414 (p7 p125 p265 p286 p342 p576 p928 : Prop)
    (h16152 : (¬ p7))
    (h15893 : p7 ∨ (¬ p125) ∨ (¬ p265) ∨ (¬ p286) ∨ (¬ p342) ∨ (¬ p576) ∨ (¬ p928)) : (¬ p125) ∨ (¬ p265) ∨ (¬ p286) ∨ (¬ p342) ∨ (¬ p576) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p342 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15893 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20415 (p7 p237 p668 p814 p835 p1116 : Prop)
    (h16152 : (¬ p7))
    (h15894 : p7 ∨ (¬ p237) ∨ (¬ p668) ∨ (¬ p814) ∨ (¬ p835) ∨ (¬ p1116)) : (¬ p237) ∨ (¬ p668) ∨ (¬ p814) ∨ (¬ p835) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p835 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15894 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20416 (p7 p43 p171 p424 p928 p1187 : Prop)
    (h16152 : (¬ p7))
    (h15895 : p7 ∨ (¬ p43) ∨ (¬ p171) ∨ (¬ p424) ∨ (¬ p928) ∨ (¬ p1187)) : (¬ p43) ∨ (¬ p171) ∨ (¬ p424) ∨ (¬ p928) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15895 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20419 (p7 p14 p71 p164 p481 p996 p1136 p1188 p1287 : Prop)
    (h16152 : (¬ p7))
    (h789 : p164)
    (h16259 : (¬ p1136))
    (h15898 : p7 ∨ (¬ p14) ∨ (¬ p71) ∨ (¬ p164) ∨ (¬ p481) ∨ (¬ p996) ∨ p1136 ∨ (¬ p1188) ∨ (¬ p1287)) : (¬ p14) ∨ (¬ p71) ∨ (¬ p481) ∨ (¬ p996) ∨ (¬ p1188) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : p164 := by
    exact h789
  have u8 : (¬ p1136) := by
    exact h16259
  rcases h15898 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u8 q6)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step20420 (p7 p43 p135 p424 p581 p1187 : Prop)
    (h16152 : (¬ p7))
    (h15899 : p7 ∨ (¬ p43) ∨ (¬ p135) ∨ (¬ p424) ∨ (¬ p581) ∨ (¬ p1187)) : (¬ p43) ∨ (¬ p135) ∨ (¬ p424) ∨ (¬ p581) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15899 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20421 (p7 p14 p106 p133 p265 p305 p481 p576 p792 p1055 p1077 p1187 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h4535 : p792)
    (h15900 : p7 ∨ (¬ p14) ∨ (¬ p106) ∨ p133 ∨ (¬ p265) ∨ (¬ p305) ∨ (¬ p481) ∨ (¬ p576) ∨ (¬ p792) ∨ (¬ p1055) ∨ (¬ p1077) ∨ (¬ p1187)) : (¬ p14) ∨ (¬ p106) ∨ (¬ p265) ∨ (¬ p305) ∨ (¬ p481) ∨ (¬ p576) ∨ (¬ p1055) ∨ (¬ p1077) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p133) := by
    exact h16157
  have u11 : p792 := by
    exact h4535
  rcases h15900 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u10 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u11)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step20422 (p7 p14 p164 p814 p1141 p1255 p1346 p1527 : Prop)
    (h16152 : (¬ p7))
    (h789 : p164)
    (h16359 : (¬ p1527))
    (h15901 : p7 ∨ (¬ p14) ∨ (¬ p164) ∨ (¬ p814) ∨ (¬ p1141) ∨ (¬ p1255) ∨ (¬ p1346) ∨ p1527) : (¬ p14) ∨ (¬ p814) ∨ (¬ p1141) ∨ (¬ p1255) ∨ (¬ p1346) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p164 := by
    exact h789
  have u7 : (¬ p1527) := by
    exact h16359
  rcases h15901 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step20423 (p7 p304 p500 p595 p726 p985 p1286 p1333 : Prop)
    (h16152 : (¬ p7))
    (h15902 : p7 ∨ (¬ p304) ∨ (¬ p500) ∨ (¬ p595) ∨ (¬ p726) ∨ (¬ p985) ∨ (¬ p1286) ∨ (¬ p1333)) : (¬ p304) ∨ (¬ p500) ∨ (¬ p595) ∨ (¬ p726) ∨ (¬ p985) ∨ (¬ p1286) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15902 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20424 (p7 p71 p304 p423 p481 p500 p1040 p1076 p1187 : Prop)
    (h16152 : (¬ p7))
    (h15903 : p7 ∨ (¬ p71) ∨ (¬ p304) ∨ (¬ p423) ∨ (¬ p481) ∨ (¬ p500) ∨ (¬ p1040) ∨ (¬ p1076) ∨ (¬ p1187)) : (¬ p71) ∨ (¬ p304) ∨ (¬ p423) ∨ (¬ p481) ∨ (¬ p500) ∨ (¬ p1040) ∨ (¬ p1076) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1040 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15903 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20425 (p7 p45 p90 p192 p226 p669 p789 p790 p1036 : Prop)
    (h16152 : (¬ p7))
    (h15904 : p7 ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p192) ∨ (¬ p226) ∨ (¬ p669) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1036)) : (¬ p45) ∨ (¬ p90) ∨ (¬ p192) ∨ (¬ p226) ∨ (¬ p669) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1036) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15904 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20426 (p2 p7 p45 p140 p192 p326 p581 : Prop)
    (h16152 : (¬ p7))
    (h15905 : (¬ p2) ∨ p7 ∨ (¬ p45) ∨ (¬ p140) ∨ (¬ p192) ∨ (¬ p326) ∨ (¬ p581)) : (¬ p2) ∨ (¬ p45) ∨ (¬ p140) ∨ (¬ p192) ∨ (¬ p326) ∨ (¬ p581) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15905 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20427 (p7 p171 p189 p241 p256 p983 p1056 p1081 p1226 p1443 : Prop)
    (h16152 : (¬ p7))
    (h15906 : p7 ∨ (¬ p171) ∨ (¬ p189) ∨ (¬ p241) ∨ (¬ p256) ∨ (¬ p983) ∨ (¬ p1056) ∨ (¬ p1081) ∨ (¬ p1226) ∨ (¬ p1443)) : (¬ p171) ∨ (¬ p189) ∨ (¬ p241) ∨ (¬ p256) ∨ (¬ p983) ∨ (¬ p1056) ∨ (¬ p1081) ∨ (¬ p1226) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1056 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15906 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20428 (p7 p102 p125 p129 p140 p189 p265 p431 p438 p790 p801 p996 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h6478 : p1075)
    (h15907 : p7 ∨ (¬ p102) ∨ (¬ p125) ∨ p129 ∨ (¬ p140) ∨ (¬ p189) ∨ (¬ p265) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p790) ∨ (¬ p801) ∨ (¬ p996) ∨ (¬ p1075)) : (¬ p102) ∨ (¬ p125) ∨ (¬ p140) ∨ (¬ p189) ∨ (¬ p265) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p790) ∨ (¬ p801) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p801 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : (¬ p129) := by
    exact h16154
  have u12 : p1075 := by
    exact h6478
  rcases h15907 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u11 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u8)
  · exact False.elim (q11 u9)
  · exact False.elim (q12 u12)

theorem step20429 (p7 p102 p140 p256 p342 p515 p814 : Prop)
    (h16152 : (¬ p7))
    (h15908 : p7 ∨ (¬ p102) ∨ (¬ p140) ∨ (¬ p256) ∨ (¬ p342) ∨ (¬ p515) ∨ (¬ p814)) : (¬ p102) ∨ (¬ p140) ∨ (¬ p256) ∨ (¬ p342) ∨ (¬ p515) ∨ (¬ p814) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p342 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p515 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15908 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20430 (p7 p15 p234 p346 p426 p996 p1055 p1077 p1103 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h6744 : p1135)
    (h15909 : p7 ∨ (¬ p15) ∨ (¬ p234) ∨ (¬ p346) ∨ p426 ∨ (¬ p996) ∨ (¬ p1055) ∨ (¬ p1077) ∨ (¬ p1103) ∨ (¬ p1135)) : (¬ p15) ∨ (¬ p234) ∨ (¬ p346) ∨ (¬ p996) ∨ (¬ p1055) ∨ (¬ p1077) ∨ (¬ p1103) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p426) := by
    exact h16178
  have u9 : p1135 := by
    exact h6744
  rcases h15909 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u8 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u9)

theorem step20431 (p7 p15 p234 p431 p710 p734 p996 p1103 : Prop)
    (h16152 : (¬ p7))
    (h15910 : p7 ∨ (¬ p15) ∨ (¬ p234) ∨ (¬ p431) ∨ (¬ p710) ∨ (¬ p734) ∨ (¬ p996) ∨ (¬ p1103)) : (¬ p15) ∨ (¬ p234) ∨ (¬ p431) ∨ (¬ p710) ∨ (¬ p734) ∨ (¬ p996) ∨ (¬ p1103) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15910 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20432 (p7 p344 p686 p728 p801 p996 p1015 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h6744 : p1135)
    (h15911 : p7 ∨ (¬ p344) ∨ p686 ∨ (¬ p728) ∨ (¬ p801) ∨ (¬ p996) ∨ (¬ p1015) ∨ (¬ p1135)) : (¬ p344) ∨ (¬ p728) ∨ (¬ p801) ∨ (¬ p996) ∨ (¬ p1015) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p801 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p686) := by
    exact h16205
  have u7 : p1135 := by
    exact h6744
  rcases h15911 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step20433 (p7 p12 p13 p135 p169 p189 p237 p265 p959 p1226 p1452 : Prop)
    (h16152 : (¬ p7))
    (h15912 : p7 ∨ (¬ p12) ∨ (¬ p13) ∨ (¬ p135) ∨ (¬ p169) ∨ (¬ p189) ∨ (¬ p237) ∨ (¬ p265) ∨ (¬ p959) ∨ (¬ p1226) ∨ (¬ p1452)) : (¬ p12) ∨ (¬ p13) ∨ (¬ p135) ∨ (¬ p169) ∨ (¬ p189) ∨ (¬ p237) ∨ (¬ p265) ∨ (¬ p959) ∨ (¬ p1226) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p169 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p959 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h15912 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)
  · exact False.elim (q10 u9)

theorem step20434 (p7 p135 p189 p237 p265 p304 p346 p668 p1116 : Prop)
    (h16152 : (¬ p7))
    (h15913 : p7 ∨ (¬ p135) ∨ (¬ p189) ∨ (¬ p237) ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p668) ∨ (¬ p1116)) : (¬ p135) ∨ (¬ p189) ∨ (¬ p237) ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p668) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15913 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20435 (p7 p10 p134 p195 p211 p362 : Prop)
    (h16152 : (¬ p7))
    (h15914 : p7 ∨ (¬ p10) ∨ (¬ p134) ∨ (¬ p195) ∨ (¬ p211) ∨ (¬ p362)) : (¬ p10) ∨ (¬ p134) ∨ (¬ p195) ∨ (¬ p211) ∨ (¬ p362) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15914 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20436 (p7 p84 p193 p424 p669 p929 p996 p1096 p1232 p1307 : Prop)
    (h16152 : (¬ p7))
    (h15915 : p7 ∨ (¬ p84) ∨ (¬ p193) ∨ (¬ p424) ∨ (¬ p669) ∨ (¬ p929) ∨ (¬ p996) ∨ (¬ p1096) ∨ (¬ p1232) ∨ (¬ p1307)) : (¬ p84) ∨ (¬ p193) ∨ (¬ p424) ∨ (¬ p669) ∨ (¬ p929) ∨ (¬ p996) ∨ (¬ p1096) ∨ (¬ p1232) ∨ (¬ p1307) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1307 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15915 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20437 (p7 p10 p102 p126 p256 p791 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16213 : (¬ p791))
    (h6478 : p1075)
    (h15916 : p7 ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p126) ∨ (¬ p256) ∨ p791 ∨ (¬ p1075)) : (¬ p10) ∨ (¬ p102) ∨ (¬ p126) ∨ (¬ p256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p791) := by
    exact h16213
  have u6 : p1075 := by
    exact h6478
  rcases h15916 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step20439 (p7 p836 p904 p1096 p1116 p1136 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16259 : (¬ p1136))
    (h6761 : p1139)
    (h15920 : p7 ∨ (¬ p836) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1116) ∨ p1136 ∨ (¬ p1139)) : (¬ p836) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p1136) := by
    exact h16259
  have u6 : p1139 := by
    exact h6761
  rcases h15920 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step20440 (p7 p19 p38 p42 p134 p168 p226 p1095 p1096 p1115 p1136 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16259 : (¬ p1136))
    (h15921 : p7 ∨ (¬ p19) ∨ (¬ p38) ∨ (¬ p42) ∨ (¬ p134) ∨ (¬ p168) ∨ (¬ p226) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1115) ∨ p1136) : (¬ p19) ∨ (¬ p38) ∨ (¬ p134) ∨ (¬ p168) ∨ (¬ p226) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p168 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p42 := by
    exact h132
  have u10 : (¬ p1136) := by
    exact h16259
  rcases h15921 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (u10 q10)

theorem step20441 (p7 p9 p39 p69 p922 p1061 p1074 : Prop)
    (h16152 : (¬ p7))
    (h15923 : p7 ∨ (¬ p9) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p922) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p9) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p922) ∨ (¬ p1061) ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p922 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15923 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20442 (p2 p7 p39 p63 p64 p234 : Prop)
    (h16152 : (¬ p7))
    (h15924 : (¬ p2) ∨ p7 ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p64) ∨ (¬ p234)) : (¬ p2) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p64) ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15924 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20444 (p7 p39 p63 p234 p669 p923 p996 p1099 p1115 : Prop)
    (h16152 : (¬ p7))
    (h15926 : p7 ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p234) ∨ (¬ p669) ∨ (¬ p923) ∨ (¬ p996) ∨ (¬ p1099) ∨ (¬ p1115)) : (¬ p39) ∨ (¬ p63) ∨ (¬ p234) ∨ (¬ p669) ∨ (¬ p923) ∨ (¬ p996) ∨ (¬ p1099) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p923 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15926 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20445 (p7 p11 p17 p39 p69 p88 p389 p595 p996 p1192 : Prop)
    (h16152 : (¬ p7))
    (h15927 : p7 ∨ (¬ p11) ∨ (¬ p17) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p389) ∨ (¬ p595) ∨ (¬ p996) ∨ (¬ p1192)) : (¬ p11) ∨ (¬ p17) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p389) ∨ (¬ p595) ∨ (¬ p996) ∨ (¬ p1192) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15927 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20446 (p7 p39 p69 p88 p258 p261 p595 p686 p961 p996 p1135 p1192 p1443 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h6744 : p1135)
    (h15928 : p7 ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p258) ∨ (¬ p261) ∨ (¬ p595) ∨ p686 ∨ (¬ p961) ∨ (¬ p996) ∨ (¬ p1135) ∨ (¬ p1192) ∨ (¬ p1443)) : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p258) ∨ (¬ p261) ∨ (¬ p595) ∨ (¬ p961) ∨ (¬ p996) ∨ (¬ p1192) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : (¬ p686) := by
    exact h16205
  have u12 : p1135 := by
    exact h6744
  rcases h15928 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u11 q7)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u12)
  · exact False.elim (q11 u8)
  · exact False.elim (q12 u9)

theorem step20447 (p7 p17 p39 p68 p88 p258 p481 p669 p996 p1076 : Prop)
    (h16152 : (¬ p7))
    (h15929 : p7 ∨ (¬ p17) ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p258) ∨ (¬ p481) ∨ (¬ p669) ∨ (¬ p996) ∨ (¬ p1076)) : (¬ p17) ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p258) ∨ (¬ p481) ∨ (¬ p669) ∨ (¬ p996) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15929 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20448 (p7 p17 p39 p69 p88 p258 p346 p426 p1225 p1229 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h8348 : p1386)
    (h15930 : p7 ∨ (¬ p17) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p258) ∨ (¬ p346) ∨ p426 ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1386)) : (¬ p17) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p258) ∨ (¬ p346) ∨ (¬ p1225) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p426) := by
    exact h16178
  have u10 : p1386 := by
    exact h8348
  rcases h15930 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u9 q7)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u10)

theorem step20449 (p7 p304 p425 p426 p836 p1076 p1116 p1530 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h9352 : p1530)
    (h15931 : p7 ∨ (¬ p304) ∨ (¬ p425) ∨ p426 ∨ (¬ p836) ∨ (¬ p1076) ∨ (¬ p1116) ∨ (¬ p1530)) : (¬ p304) ∨ (¬ p425) ∨ (¬ p836) ∨ (¬ p1076) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
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
  have u4 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p426) := by
    exact h16178
  have u7 : p1530 := by
    exact h9352
  rcases h15931 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step20451 (p7 p39 p69 p88 p238 p426 p595 p836 p1055 p1116 p1135 p1286 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h6744 : p1135)
    (h15933 : p7 ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p238) ∨ p426 ∨ (¬ p595) ∨ (¬ p836) ∨ (¬ p1055) ∨ (¬ p1116) ∨ (¬ p1135) ∨ (¬ p1286)) : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p238) ∨ (¬ p595) ∨ (¬ p836) ∨ (¬ p1055) ∨ (¬ p1116) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p426) := by
    exact h16178
  have u11 : p1135 := by
    exact h6744
  rcases h15933 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u10 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u11)
  · exact False.elim (q11 u8)

theorem step20452 (p7 p190 p261 p305 p426 p435 p475 p687 p836 p996 p1055 p1116 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h6744 : p1135)
    (h15934 : p7 ∨ (¬ p190) ∨ (¬ p261) ∨ (¬ p305) ∨ p426 ∨ (¬ p435) ∨ (¬ p475) ∨ (¬ p687) ∨ (¬ p836) ∨ (¬ p996) ∨ (¬ p1055) ∨ (¬ p1116) ∨ (¬ p1135)) : (¬ p190) ∨ (¬ p261) ∨ (¬ p305) ∨ (¬ p435) ∨ (¬ p475) ∨ (¬ p687) ∨ (¬ p836) ∨ (¬ p996) ∨ (¬ p1055) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p475 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : (¬ p426) := by
    exact h16178
  have u12 : p1135 := by
    exact h6744
  rcases h15934 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u11 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u8)
  · exact False.elim (q11 u9)
  · exact False.elim (q12 u12)

theorem step20453 (p7 p11 p17 p39 p68 p88 p481 p532 p1330 p1366 : Prop)
    (h16152 : (¬ p7))
    (h15935 : p7 ∨ (¬ p11) ∨ (¬ p17) ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p481) ∨ (¬ p532) ∨ (¬ p1330) ∨ (¬ p1366)) : (¬ p11) ∨ (¬ p17) ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p481) ∨ (¬ p532) ∨ (¬ p1330) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15935 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20454 (p7 p308 p344 p836 p1055 p1116 : Prop)
    (h16152 : (¬ p7))
    (h15936 : p7 ∨ (¬ p308) ∨ (¬ p344) ∨ (¬ p836) ∨ (¬ p1055) ∨ (¬ p1116)) : (¬ p308) ∨ (¬ p344) ∨ (¬ p836) ∨ (¬ p1055) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p308 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15936 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20455 (p7 p11 p39 p68 p88 p261 p288 p304 p389 p481 p996 : Prop)
    (h16152 : (¬ p7))
    (h15937 : p7 ∨ (¬ p11) ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p261) ∨ (¬ p288) ∨ (¬ p304) ∨ (¬ p389) ∨ (¬ p481) ∨ (¬ p996)) : (¬ p11) ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p261) ∨ (¬ p288) ∨ (¬ p304) ∨ (¬ p389) ∨ (¬ p481) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h15937 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)
  · exact False.elim (q10 u9)

theorem step20456 (p7 p39 p69 p88 p185 p595 p669 p996 p1115 p1192 : Prop)
    (h16152 : (¬ p7))
    (h15938 : p7 ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p185) ∨ (¬ p595) ∨ (¬ p669) ∨ (¬ p996) ∨ (¬ p1115) ∨ (¬ p1192)) : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p185) ∨ (¬ p595) ∨ (¬ p669) ∨ (¬ p996) ∨ (¬ p1115) ∨ (¬ p1192) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p88 := by
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
  have u5 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15938 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20457 (p7 p264 p959 p1226 p1443 p1452 : Prop)
    (h16152 : (¬ p7))
    (h15939 : p7 ∨ (¬ p264) ∨ (¬ p959) ∨ (¬ p1226) ∨ (¬ p1443) ∨ (¬ p1452)) : (¬ p264) ∨ (¬ p959) ∨ (¬ p1226) ∨ (¬ p1443) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p264 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p959 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15939 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20458 (p7 p126 p499 p578 p597 p616 : Prop)
    (h16152 : (¬ p7))
    (h15940 : p7 ∨ (¬ p126) ∨ (¬ p499) ∨ (¬ p578) ∨ (¬ p597) ∨ (¬ p616)) : (¬ p126) ∨ (¬ p499) ∨ (¬ p578) ∨ (¬ p597) ∨ (¬ p616) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p578 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p597 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15940 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20459 (p7 p261 p288 p301 p304 p327 p435 p687 p817 : Prop)
    (h16152 : (¬ p7))
    (h15941 : p7 ∨ (¬ p261) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p304) ∨ (¬ p327) ∨ (¬ p435) ∨ (¬ p687) ∨ (¬ p817)) : (¬ p261) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p304) ∨ (¬ p327) ∨ (¬ p435) ∨ (¬ p687) ∨ (¬ p817) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p817 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15941 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20460 (p7 p190 p261 p286 p304 p481 p980 p1115 p1330 p1366 : Prop)
    (h16152 : (¬ p7))
    (h15942 : p7 ∨ (¬ p190) ∨ (¬ p261) ∨ (¬ p286) ∨ (¬ p304) ∨ (¬ p481) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p1330) ∨ (¬ p1366)) : (¬ p190) ∨ (¬ p261) ∨ (¬ p286) ∨ (¬ p304) ∨ (¬ p481) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p1330) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15942 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20461 (p7 p39 p69 p88 p983 p1229 p1309 p1349 p1489 : Prop)
    (h16152 : (¬ p7))
    (h15943 : p7 ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p983) ∨ (¬ p1229) ∨ (¬ p1309) ∨ (¬ p1349) ∨ (¬ p1489)) : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p983) ∨ (¬ p1229) ∨ (¬ p1309) ∨ (¬ p1349) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15943 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20463 (p7 p426 p836 p983 p1116 p1135 p1325 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h6744 : p1135)
    (h15945 : p7 ∨ p426 ∨ (¬ p836) ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1135) ∨ (¬ p1325)) : (¬ p836) ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p426) := by
    exact h16178
  have u6 : p1135 := by
    exact h6744
  rcases h15945 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step20464 (p2 p3 p7 p12 p540 p668 : Prop)
    (h16152 : (¬ p7))
    (h15946 : (¬ p2) ∨ (¬ p3) ∨ p7 ∨ (¬ p12) ∨ (¬ p540) ∨ (¬ p668)) : (¬ p2) ∨ (¬ p3) ∨ (¬ p12) ∨ (¬ p540) ∨ (¬ p668) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15946 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20465 (p3 p7 p12 p17 p190 p258 p346 p668 : Prop)
    (h16152 : (¬ p7))
    (h15947 : (¬ p3) ∨ p7 ∨ (¬ p12) ∨ (¬ p17) ∨ (¬ p190) ∨ (¬ p258) ∨ (¬ p346) ∨ (¬ p668)) : (¬ p3) ∨ (¬ p12) ∨ (¬ p17) ∨ (¬ p190) ∨ (¬ p258) ∨ (¬ p346) ∨ (¬ p668) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p12 := by
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
  have u4 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15947 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20466 (p7 p8 p63 p389 p456 p495 p657 p924 p1098 : Prop)
    (h16152 : (¬ p7))
    (h15948 : p7 ∨ (¬ p8) ∨ (¬ p63) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p657) ∨ (¬ p924) ∨ (¬ p1098)) : (¬ p8) ∨ (¬ p63) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p657) ∨ (¬ p924) ∨ (¬ p1098) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1098 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15948 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20467 (p7 p63 p69 p224 p406 p545 p680 p924 p1098 p1187 : Prop)
    (h16152 : (¬ p7))
    (h15949 : p7 ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p224) ∨ (¬ p406) ∨ (¬ p545) ∨ (¬ p680) ∨ (¬ p924) ∨ (¬ p1098) ∨ (¬ p1187)) : (¬ p63) ∨ (¬ p69) ∨ (¬ p224) ∨ (¬ p406) ∨ (¬ p545) ∨ (¬ p680) ∨ (¬ p924) ∨ (¬ p1098) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1098 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15949 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20468 (p7 p63 p344 p686 p792 p897 p1099 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h4535 : p792)
    (h15950 : p7 ∨ (¬ p63) ∨ (¬ p344) ∨ p686 ∨ (¬ p792) ∨ (¬ p897) ∨ (¬ p1099)) : (¬ p63) ∨ (¬ p344) ∨ (¬ p897) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p686) := by
    exact h16205
  have u6 : p792 := by
    exact h4535
  rcases h15950 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step20469 (p7 p190 p258 p261 p481 p686 p996 p1333 p1386 p1624 p1651 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h8348 : p1386)
    (h15951 : p7 ∨ (¬ p190) ∨ (¬ p258) ∨ (¬ p261) ∨ (¬ p481) ∨ p686 ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p1386) ∨ (¬ p1624) ∨ (¬ p1651)) : (¬ p190) ∨ (¬ p258) ∨ (¬ p261) ∨ (¬ p481) ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p1624) ∨ (¬ p1651) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1651 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p686) := by
    exact h16205
  have u10 : p1386 := by
    exact h8348
  rcases h15951 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u9 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step20470 (p7 p39 p63 p68 p224 p481 p616 p906 p996 : Prop)
    (h16152 : (¬ p7))
    (h15952 : p7 ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p224) ∨ (¬ p481) ∨ (¬ p616) ∨ (¬ p906) ∨ (¬ p996)) : (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p224) ∨ (¬ p481) ∨ (¬ p616) ∨ (¬ p906) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p906 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15952 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20471 (p7 p63 p68 p229 p389 p456 p481 p495 p653 p792 p996 : Prop)
    (h16152 : (¬ p7))
    (h16194 : (¬ p653))
    (h4535 : p792)
    (h15953 : p7 ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p229) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p481) ∨ (¬ p495) ∨ p653 ∨ (¬ p792) ∨ (¬ p996)) : (¬ p63) ∨ (¬ p68) ∨ (¬ p229) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p481) ∨ (¬ p495) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p653) := by
    exact h16194
  have u10 : p792 := by
    exact h4535
  rcases h15953 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (u9 q8)
  · exact False.elim (q9 u10)
  · exact False.elim (q10 u7)

theorem step20472 (p7 p8 p12 p39 p63 p68 p225 p561 p1232 p1313 : Prop)
    (h16152 : (¬ p7))
    (h15954 : p7 ∨ (¬ p8) ∨ (¬ p12) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p225) ∨ (¬ p561) ∨ (¬ p1232) ∨ (¬ p1313)) : (¬ p8) ∨ (¬ p12) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p225) ∨ (¬ p561) ∨ (¬ p1232) ∨ (¬ p1313) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1313 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15954 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20473 (p3 p7 p39 p63 p68 p544 p657 p864 p1232 p1269 : Prop)
    (h16152 : (¬ p7))
    (h15955 : (¬ p3) ∨ p7 ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p544) ∨ (¬ p657) ∨ (¬ p864) ∨ (¬ p1232) ∨ (¬ p1269)) : (¬ p3) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p544) ∨ (¬ p657) ∨ (¬ p864) ∨ (¬ p1232) ∨ (¬ p1269) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1269 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15955 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (u9 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20475 (p7 p63 p435 p996 p1232 p1295 p1389 p1542 : Prop)
    (h16152 : (¬ p7))
    (h15958 : p7 ∨ (¬ p63) ∨ (¬ p435) ∨ (¬ p996) ∨ (¬ p1232) ∨ (¬ p1295) ∨ (¬ p1389) ∨ (¬ p1542)) : (¬ p63) ∨ (¬ p435) ∨ (¬ p996) ∨ (¬ p1232) ∨ (¬ p1295) ∨ (¬ p1389) ∨ (¬ p1542) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1295 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15958 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20476 (p7 p39 p63 p68 p561 p864 p983 p1061 p1232 p1269 p1325 : Prop)
    (h16152 : (¬ p7))
    (h15959 : p7 ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p561) ∨ (¬ p864) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1232) ∨ (¬ p1269) ∨ (¬ p1325)) : (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p561) ∨ (¬ p864) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1232) ∨ (¬ p1269) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1269 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h15959 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)
  · exact False.elim (q10 u9)

theorem step20477 (p7 p8 p39 p63 p68 p540 p561 p996 p1333 p1431 p1667 : Prop)
    (h16152 : (¬ p7))
    (h15960 : p7 ∨ (¬ p8) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p540) ∨ (¬ p561) ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p1431) ∨ (¬ p1667)) : (¬ p8) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p540) ∨ (¬ p561) ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p1431) ∨ (¬ p1667) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h15960 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)
  · exact False.elim (q10 u9)

theorem step20478 (p7 p8 p40 p69 p540 p563 p940 p996 p1333 p1386 p1570 p1674 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h8348 : p1386)
    (h15961 : p7 ∨ (¬ p8) ∨ p40 ∨ (¬ p69) ∨ (¬ p540) ∨ (¬ p563) ∨ (¬ p940) ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p1386) ∨ (¬ p1570) ∨ (¬ p1674)) : (¬ p8) ∨ (¬ p69) ∨ (¬ p540) ∨ (¬ p563) ∨ (¬ p940) ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p1570) ∨ (¬ p1674) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p563 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1570 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1674 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p40) := by
    exact h16150
  have u11 : p1386 := by
    exact h8348
  rcases h15961 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u10 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u11)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step20479 (p7 p17 p88 p534 p758 p924 p1036 p1061 p1098 p1644 : Prop)
    (h16152 : (¬ p7))
    (h15962 : p7 ∨ (¬ p17) ∨ (¬ p88) ∨ (¬ p534) ∨ (¬ p758) ∨ (¬ p924) ∨ (¬ p1036) ∨ (¬ p1061) ∨ (¬ p1098) ∨ (¬ p1644)) : (¬ p17) ∨ (¬ p88) ∨ (¬ p534) ∨ (¬ p758) ∨ (¬ p924) ∨ (¬ p1036) ∨ (¬ p1061) ∨ (¬ p1098) ∨ (¬ p1644) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p758 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1098 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15962 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20480 (p7 p39 p63 p68 p426 p481 p897 p996 p1099 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h8348 : p1386)
    (h15963 : p7 ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ p426 ∨ (¬ p481) ∨ (¬ p897) ∨ (¬ p996) ∨ (¬ p1099) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p481) ∨ (¬ p897) ∨ (¬ p996) ∨ (¬ p1099) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p426) := by
    exact h16178
  have u10 : p1386 := by
    exact h8348
  rcases h15963 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u9 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u10)

theorem step20481 (p7 p39 p69 p88 p185 p668 p836 p1095 p1096 : Prop)
    (h16152 : (¬ p7))
    (h15965 : p7 ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p185) ∨ (¬ p668) ∨ (¬ p836) ∨ (¬ p1095) ∨ (¬ p1096)) : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p185) ∨ (¬ p668) ∨ (¬ p836) ∨ (¬ p1095) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15965 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20482 (p7 p40 p69 p224 p343 p595 p1286 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h1950 : p343)
    (h15966 : p7 ∨ p40 ∨ (¬ p69) ∨ (¬ p224) ∨ (¬ p343) ∨ (¬ p595) ∨ (¬ p1286)) : (¬ p69) ∨ (¬ p224) ∨ (¬ p595) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p40) := by
    exact h16150
  have u6 : p343 := by
    exact h1950
  rcases h15966 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step20483 (p7 p40 p69 p657 p904 p1096 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h6744 : p1135)
    (h15967 : p7 ∨ p40 ∨ (¬ p69) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1135)) : (¬ p69) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p40) := by
    exact h16150
  have u6 : p1135 := by
    exact h6744
  rcases h15967 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step20485 (p7 p123 p288 p595 p635 p1099 p1135 p1286 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h6744 : p1135)
    (h15969 : p7 ∨ p123 ∨ (¬ p288) ∨ (¬ p595) ∨ (¬ p635) ∨ (¬ p1099) ∨ (¬ p1135) ∨ (¬ p1286)) : (¬ p288) ∨ (¬ p595) ∨ (¬ p635) ∨ (¬ p1099) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p635 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p123) := by
    exact h16186
  have u7 : p1135 := by
    exact h6744
  rcases h15969 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step20486 (p7 p8 p11 p12 p13 p17 p190 p225 p561 : Prop)
    (h16152 : (¬ p7))
    (h15970 : p7 ∨ (¬ p8) ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p13) ∨ (¬ p17) ∨ (¬ p190) ∨ (¬ p225) ∨ (¬ p561)) : (¬ p8) ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p13) ∨ (¬ p17) ∨ (¬ p190) ∨ (¬ p225) ∨ (¬ p561) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15970 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20487 (p3 p7 p11 p17 p190 p389 p544 p657 : Prop)
    (h16152 : (¬ p7))
    (h15971 : (¬ p3) ∨ p7 ∨ (¬ p11) ∨ (¬ p17) ∨ (¬ p190) ∨ (¬ p389) ∨ (¬ p544) ∨ (¬ p657)) : (¬ p3) ∨ (¬ p11) ∨ (¬ p17) ∨ (¬ p190) ∨ (¬ p389) ∨ (¬ p544) ∨ (¬ p657) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
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
  have u4 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15971 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20488 (p7 p8 p12 p190 p225 p258 p261 p561 p686 p961 p1139 p1443 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h6761 : p1139)
    (h15972 : p7 ∨ (¬ p8) ∨ (¬ p12) ∨ (¬ p190) ∨ (¬ p225) ∨ (¬ p258) ∨ (¬ p261) ∨ (¬ p561) ∨ p686 ∨ (¬ p961) ∨ (¬ p1139) ∨ (¬ p1443)) : (¬ p8) ∨ (¬ p12) ∨ (¬ p190) ∨ (¬ p225) ∨ (¬ p258) ∨ (¬ p261) ∨ (¬ p561) ∨ (¬ p961) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p686) := by
    exact h16205
  have u11 : p1139 := by
    exact h6761
  rcases h15972 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (u10 q8)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u11)
  · exact False.elim (q11 u8)

theorem step20489 (p7 p39 p69 p227 p456 p498 p575 : Prop)
    (h16152 : (¬ p7))
    (h15973 : p7 ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p227) ∨ (¬ p456) ∨ (¬ p498) ∨ (¬ p575)) : (¬ p39) ∨ (¬ p69) ∨ (¬ p227) ∨ (¬ p456) ∨ (¬ p498) ∨ (¬ p575) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p575 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15973 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20491 (p7 p27 p101 p495 p639 p1096 : Prop)
    (h16152 : (¬ p7))
    (h15975 : p7 ∨ (¬ p27) ∨ (¬ p101) ∨ (¬ p495) ∨ (¬ p639) ∨ (¬ p1096)) : (¬ p27) ∨ (¬ p101) ∨ (¬ p495) ∨ (¬ p639) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p27 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p639 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15975 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20492 (p7 p12 p14 p15 p16 p185 p668 p836 : Prop)
    (h16152 : (¬ p7))
    (h15976 : p7 ∨ (¬ p12) ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p185) ∨ (¬ p668) ∨ (¬ p836)) : (¬ p12) ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p185) ∨ (¬ p668) ∨ (¬ p836) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15976 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20493 (p7 p19 p126 p143 p325 p1187 : Prop)
    (h16152 : (¬ p7))
    (h15977 : p7 ∨ (¬ p19) ∨ (¬ p126) ∨ (¬ p143) ∨ (¬ p325) ∨ (¬ p1187)) : (¬ p19) ∨ (¬ p126) ∨ (¬ p143) ∨ (¬ p325) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15977 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20494 (p7 p16 p71 p185 p423 p481 p1040 p1115 p1187 : Prop)
    (h16152 : (¬ p7))
    (h15978 : p7 ∨ (¬ p16) ∨ (¬ p71) ∨ (¬ p185) ∨ (¬ p423) ∨ (¬ p481) ∨ (¬ p1040) ∨ (¬ p1115) ∨ (¬ p1187)) : (¬ p16) ∨ (¬ p71) ∨ (¬ p185) ∨ (¬ p423) ∨ (¬ p481) ∨ (¬ p1040) ∨ (¬ p1115) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1040 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15978 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20495 (p7 p16 p17 p258 p595 p669 p1076 p1286 : Prop)
    (h16152 : (¬ p7))
    (h15979 : p7 ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p258) ∨ (¬ p595) ∨ (¬ p669) ∨ (¬ p1076) ∨ (¬ p1286)) : (¬ p16) ∨ (¬ p17) ∨ (¬ p258) ∨ (¬ p595) ∨ (¬ p669) ∨ (¬ p1076) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15979 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20496 (p7 p16 p17 p224 p301 p351 p595 p1286 : Prop)
    (h16152 : (¬ p7))
    (h15980 : p7 ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p224) ∨ (¬ p301) ∨ (¬ p351) ∨ (¬ p595) ∨ (¬ p1286)) : (¬ p16) ∨ (¬ p17) ∨ (¬ p224) ∨ (¬ p301) ∨ (¬ p351) ∨ (¬ p595) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15980 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20497 (p7 p15 p16 p106 p185 p344 p423 p836 p1037 : Prop)
    (h16152 : (¬ p7))
    (h15981 : p7 ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p106) ∨ (¬ p185) ∨ (¬ p344) ∨ (¬ p423) ∨ (¬ p836) ∨ (¬ p1037)) : (¬ p15) ∨ (¬ p16) ∨ (¬ p106) ∨ (¬ p185) ∨ (¬ p344) ∨ (¬ p423) ∨ (¬ p836) ∨ (¬ p1037) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1037 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15981 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20498 (p7 p19 p326 p406 p476 p1188 p1287 : Prop)
    (h16152 : (¬ p7))
    (h15982 : p7 ∨ (¬ p19) ∨ (¬ p326) ∨ (¬ p406) ∨ (¬ p476) ∨ (¬ p1188) ∨ (¬ p1287)) : (¬ p19) ∨ (¬ p326) ∨ (¬ p406) ∨ (¬ p476) ∨ (¬ p1188) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p476 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15982 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20499 (p7 p15 p19 p170 p326 p796 p1055 p1103 p1116 : Prop)
    (h16152 : (¬ p7))
    (h15983 : p7 ∨ (¬ p15) ∨ (¬ p19) ∨ (¬ p170) ∨ (¬ p326) ∨ (¬ p796) ∨ (¬ p1055) ∨ (¬ p1103) ∨ (¬ p1116)) : (¬ p15) ∨ (¬ p19) ∨ (¬ p170) ∨ (¬ p326) ∨ (¬ p796) ∨ (¬ p1055) ∨ (¬ p1103) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15983 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20500 (p7 p141 p210 p288 p304 p326 p796 : Prop)
    (h16152 : (¬ p7))
    (h15984 : p7 ∨ (¬ p141) ∨ (¬ p210) ∨ (¬ p288) ∨ (¬ p304) ∨ (¬ p326) ∨ (¬ p796)) : (¬ p141) ∨ (¬ p210) ∨ (¬ p288) ∨ (¬ p304) ∨ (¬ p326) ∨ (¬ p796) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15984 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20501 (p7 p16 p17 p19 p258 p346 p406 p426 p620 p788 p1188 p1287 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h5066 : p788)
    (h15985 : p7 ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p19) ∨ (¬ p258) ∨ (¬ p346) ∨ (¬ p406) ∨ p426 ∨ (¬ p620) ∨ (¬ p788) ∨ (¬ p1188) ∨ (¬ p1287)) : (¬ p16) ∨ (¬ p17) ∨ (¬ p19) ∨ (¬ p258) ∨ (¬ p346) ∨ (¬ p406) ∨ (¬ p620) ∨ (¬ p1188) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p620 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p426) := by
    exact h16178
  have u11 : p788 := by
    exact h5066
  rcases h15985 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u10 q7)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u11)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step20503 (p7 p258 p346 p426 p681 p961 p1443 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h3892 : p681)
    (h15987 : p7 ∨ (¬ p258) ∨ (¬ p346) ∨ p426 ∨ (¬ p681) ∨ (¬ p961) ∨ (¬ p1443)) : (¬ p258) ∨ (¬ p346) ∨ (¬ p961) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p426) := by
    exact h16178
  have u6 : p681 := by
    exact h3892
  rcases h15987 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step20504 (p7 p19 p129 p424 p788 p1188 p1366 p1545 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h5066 : p788)
    (h15988 : p7 ∨ (¬ p19) ∨ p129 ∨ (¬ p424) ∨ (¬ p788) ∨ (¬ p1188) ∨ (¬ p1366) ∨ (¬ p1545)) : (¬ p19) ∨ (¬ p424) ∨ (¬ p1188) ∨ (¬ p1366) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p788 := by
    exact h5066
  rcases h15988 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step20505 (p7 p304 p500 p595 p980 p1076 p1330 p1542 : Prop)
    (h16152 : (¬ p7))
    (h15989 : p7 ∨ (¬ p304) ∨ (¬ p500) ∨ (¬ p595) ∨ (¬ p980) ∨ (¬ p1076) ∨ (¬ p1330) ∨ (¬ p1542)) : (¬ p304) ∨ (¬ p500) ∨ (¬ p595) ∨ (¬ p980) ∨ (¬ p1076) ∨ (¬ p1330) ∨ (¬ p1542) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15989 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20506 (p3 p7 p164 p280 p301 p1159 p1208 p1443 : Prop)
    (h16152 : (¬ p7))
    (h789 : p164)
    (h16173 : (¬ p280))
    (h15990 : (¬ p3) ∨ p7 ∨ (¬ p164) ∨ p280 ∨ (¬ p301) ∨ (¬ p1159) ∨ (¬ p1208) ∨ (¬ p1443)) : (¬ p3) ∨ (¬ p301) ∨ (¬ p1159) ∨ (¬ p1208) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1208 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p164 := by
    exact h789
  have u7 : (¬ p280) := by
    exact h16173
  rcases h15990 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (u7 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step20507 (p7 p11 p15 p288 p304 p423 p500 p1210 : Prop)
    (h16152 : (¬ p7))
    (h15991 : p7 ∨ (¬ p11) ∨ (¬ p15) ∨ (¬ p288) ∨ (¬ p304) ∨ (¬ p423) ∨ (¬ p500) ∨ (¬ p1210)) : (¬ p11) ∨ (¬ p15) ∨ (¬ p288) ∨ (¬ p304) ∨ (¬ p423) ∨ (¬ p500) ∨ (¬ p1210) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15991 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20508 (p7 p16 p17 p258 p346 p668 p1095 p1096 : Prop)
    (h16152 : (¬ p7))
    (h15993 : p7 ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p258) ∨ (¬ p346) ∨ (¬ p668) ∨ (¬ p1095) ∨ (¬ p1096)) : (¬ p16) ∨ (¬ p17) ∨ (¬ p258) ∨ (¬ p346) ∨ (¬ p668) ∨ (¬ p1095) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15993 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20509 (p7 p258 p346 p668 p1082 p1443 : Prop)
    (h16152 : (¬ p7))
    (h15994 : p7 ∨ (¬ p258) ∨ (¬ p346) ∨ (¬ p668) ∨ (¬ p1082) ∨ (¬ p1443)) : (¬ p258) ∨ (¬ p346) ∨ (¬ p668) ∨ (¬ p1082) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1082 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15994 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20510 (p7 p258 p500 p657 p686 p904 p961 p1096 p1135 p1443 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h6744 : p1135)
    (h15995 : p7 ∨ (¬ p258) ∨ (¬ p500) ∨ (¬ p657) ∨ p686 ∨ (¬ p904) ∨ (¬ p961) ∨ (¬ p1096) ∨ (¬ p1135) ∨ (¬ p1443)) : (¬ p258) ∨ (¬ p500) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p961) ∨ (¬ p1096) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p686) := by
    exact h16205
  have u9 : p1135 := by
    exact h6744
  rcases h15995 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u8 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u9)
  · exact False.elim (q9 u6)

theorem step20511 (p7 p11 p16 p17 p389 p657 p904 p1096 : Prop)
    (h16152 : (¬ p7))
    (h15996 : p7 ∨ (¬ p11) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p389) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1096)) : (¬ p11) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p389) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15996 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20512 (p7 p11 p288 p304 p389 p500 p595 p1286 : Prop)
    (h16152 : (¬ p7))
    (h15997 : p7 ∨ (¬ p11) ∨ (¬ p288) ∨ (¬ p304) ∨ (¬ p389) ∨ (¬ p500) ∨ (¬ p595) ∨ (¬ p1286)) : (¬ p11) ∨ (¬ p288) ∨ (¬ p304) ∨ (¬ p389) ∨ (¬ p500) ∨ (¬ p595) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15997 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20513 (p7 p280 p301 p1443 p1452 p1465 p1708 : Prop)
    (h16152 : (¬ p7))
    (h16173 : (¬ p280))
    (h10766 : p1708)
    (h15998 : p7 ∨ p280 ∨ (¬ p301) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p1465) ∨ (¬ p1708)) : (¬ p301) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p280) := by
    exact h16173
  have u6 : p1708 := by
    exact h10766
  rcases h15998 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step20515 (p7 p19 p158 p426 p788 p836 p879 p1061 p1074 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h5066 : p788)
    (h16000 : p7 ∨ (¬ p19) ∨ (¬ p158) ∨ p426 ∨ (¬ p788) ∨ (¬ p836) ∨ (¬ p879) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p19) ∨ (¬ p158) ∨ (¬ p836) ∨ (¬ p879) ∨ (¬ p1061) ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p879 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p426) := by
    exact h16178
  have u8 : p788 := by
    exact h5066
  rcases h16000 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u7 q3)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step20516 (p7 p258 p638 p754 p1538 p1651 : Prop)
    (h16152 : (¬ p7))
    (h16001 : p7 ∨ (¬ p258) ∨ (¬ p638) ∨ (¬ p754) ∨ (¬ p1538) ∨ (¬ p1651)) : (¬ p258) ∨ (¬ p638) ∨ (¬ p754) ∨ (¬ p1538) ∨ (¬ p1651) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p638 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p754 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1651 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h16001 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20517 (p7 p15 p125 p234 p431 p438 p500 p996 : Prop)
    (h16152 : (¬ p7))
    (h16002 : p7 ∨ (¬ p15) ∨ (¬ p125) ∨ (¬ p234) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p500) ∨ (¬ p996)) : (¬ p15) ∨ (¬ p125) ∨ (¬ p234) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p500) ∨ (¬ p996) := by
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
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h16002 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20518 (p7 p84 p135 p185 p187 p426 p435 p475 p581 p687 p836 p996 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h6744 : p1135)
    (h16003 : p7 ∨ p84 ∨ (¬ p135) ∨ (¬ p185) ∨ (¬ p187) ∨ p426 ∨ (¬ p435) ∨ (¬ p475) ∨ (¬ p581) ∨ (¬ p687) ∨ (¬ p836) ∨ (¬ p996) ∨ (¬ p1135)) : p84 ∨ (¬ p135) ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p435) ∨ (¬ p475) ∨ (¬ p581) ∨ (¬ p687) ∨ (¬ p836) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p84) := fun hu => hn (Or.inl hu)
  have u1 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p475 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : (¬ p426) := by
    exact h16178
  have u12 : p1135 := by
    exact h6744
  rcases h16003 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (u10 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u11 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u8)
  · exact False.elim (q11 u9)
  · exact False.elim (q12 u12)

theorem step20519 (p7 p8 p135 p187 p561 p581 p897 p922 : Prop)
    (h16152 : (¬ p7))
    (h16004 : p7 ∨ (¬ p8) ∨ (¬ p135) ∨ (¬ p187) ∨ (¬ p561) ∨ (¬ p581) ∨ (¬ p897) ∨ (¬ p922)) : (¬ p8) ∨ (¬ p135) ∨ (¬ p187) ∨ (¬ p561) ∨ (¬ p581) ∨ (¬ p897) ∨ (¬ p922) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p922 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h16004 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20520 (p7 p12 p225 p904 p1096 p1136 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16259 : (¬ p1136))
    (h6761 : p1139)
    (h16005 : p7 ∨ (¬ p12) ∨ (¬ p225) ∨ (¬ p904) ∨ (¬ p1096) ∨ p1136 ∨ (¬ p1139)) : (¬ p12) ∨ (¬ p225) ∨ (¬ p904) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p1136) := by
    exact h16259
  have u6 : p1139 := by
    exact h6761
  rcases h16005 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step20522 (p7 p88 p132 p185 p280 p434 p581 p668 p690 p709 p836 p1061 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16173 : (¬ p280))
    (h16007 : p7 ∨ (¬ p88) ∨ (¬ p132) ∨ (¬ p185) ∨ p280 ∨ (¬ p434) ∨ (¬ p581) ∨ (¬ p668) ∨ (¬ p690) ∨ (¬ p709) ∨ (¬ p836) ∨ (¬ p1061)) : (¬ p88) ∨ (¬ p185) ∨ (¬ p434) ∨ (¬ p581) ∨ (¬ p668) ∨ (¬ p690) ∨ (¬ p709) ∨ (¬ p836) ∨ (¬ p1061) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p132 := by
    exact h786
  have u11 : (¬ p280) := by
    exact h16173
  rcases h16007 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u1)
  · exact False.elim (u11 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step20523 (p7 p19 p42 p48 p134 p237 p791 p918 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16213 : (¬ p791))
    (h16008 : p7 ∨ (¬ p19) ∨ (¬ p42) ∨ (¬ p48) ∨ (¬ p134) ∨ (¬ p237) ∨ p791 ∨ (¬ p918)) : (¬ p19) ∨ (¬ p48) ∨ (¬ p134) ∨ (¬ p237) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p791) := by
    exact h16213
  rcases h16008 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step20524 (p3 p7 p71 p229 p234 p996 p1135 p1136 : Prop)
    (h16152 : (¬ p7))
    (h6744 : p1135)
    (h16259 : (¬ p1136))
    (h16009 : (¬ p3) ∨ p7 ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p234) ∨ (¬ p996) ∨ (¬ p1135) ∨ p1136) : (¬ p3) ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p234) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p1135 := by
    exact h6744
  have u7 : (¬ p1136) := by
    exact h16259
  rcases h16009 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u6)
  · exact False.elim (u7 q7)

theorem step20525 (p7 p19 p105 p406 p557 p680 p1188 p1287 : Prop)
    (h16152 : (¬ p7))
    (h16010 : p7 ∨ (¬ p19) ∨ (¬ p105) ∨ (¬ p406) ∨ (¬ p557) ∨ (¬ p680) ∨ (¬ p1188) ∨ (¬ p1287)) : (¬ p19) ∨ (¬ p105) ∨ (¬ p406) ∨ (¬ p557) ∨ (¬ p680) ∨ (¬ p1188) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h16010 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20526 (p7 p63 p224 p343 p789 p839 p928 p1136 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16259 : (¬ p1136))
    (h16011 : p7 ∨ (¬ p63) ∨ (¬ p224) ∨ (¬ p343) ∨ (¬ p789) ∨ (¬ p839) ∨ (¬ p928) ∨ p1136) : (¬ p63) ∨ (¬ p224) ∨ (¬ p789) ∨ (¬ p839) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p839 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p343 := by
    exact h1950
  have u7 : (¬ p1136) := by
    exact h16259
  rcases h16011 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step20527 (p7 p90 p224 p237 p265 p351 p386 p576 p903 p923 p961 p1286 : Prop)
    (h16152 : (¬ p7))
    (h16012 : p7 ∨ (¬ p90) ∨ (¬ p224) ∨ (¬ p237) ∨ (¬ p265) ∨ (¬ p351) ∨ (¬ p386) ∨ (¬ p576) ∨ (¬ p903) ∨ (¬ p923) ∨ (¬ p961) ∨ (¬ p1286)) : (¬ p90) ∨ (¬ p224) ∨ (¬ p237) ∨ (¬ p265) ∨ (¬ p351) ∨ (¬ p386) ∨ (¬ p576) ∨ (¬ p903) ∨ (¬ p923) ∨ (¬ p961) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p386 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p903 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p923 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : (¬ p7) := by
    exact h16152
  rcases h16012 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u11 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)
  · exact False.elim (q10 u9)
  · exact False.elim (q11 u10)

theorem step20528 (p7 p406 p663 p715 p904 p1074 : Prop)
    (h16152 : (¬ p7))
    (h16013 : p7 ∨ (¬ p406) ∨ (¬ p663) ∨ (¬ p715) ∨ (¬ p904) ∨ (¬ p1074)) : (¬ p406) ∨ (¬ p663) ∨ (¬ p715) ∨ (¬ p904) ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p663 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p715 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h16013 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20529 (p7 p90 p237 p265 p389 p576 p657 p840 p961 : Prop)
    (h16152 : (¬ p7))
    (h16014 : p7 ∨ (¬ p90) ∨ (¬ p237) ∨ (¬ p265) ∨ (¬ p389) ∨ (¬ p576) ∨ (¬ p657) ∨ (¬ p840) ∨ (¬ p961)) : (¬ p90) ∨ (¬ p237) ∨ (¬ p265) ∨ (¬ p389) ∨ (¬ p576) ∨ (¬ p657) ∨ (¬ p840) ∨ (¬ p961) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h16014 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20530 (p7 p106 p227 p237 p304 p788 p791 p1036 p1116 p1206 : Prop)
    (h16152 : (¬ p7))
    (h5066 : p788)
    (h16213 : (¬ p791))
    (h16015 : p7 ∨ (¬ p106) ∨ (¬ p227) ∨ (¬ p237) ∨ (¬ p304) ∨ (¬ p788) ∨ p791 ∨ (¬ p1036) ∨ (¬ p1116) ∨ (¬ p1206)) : (¬ p106) ∨ (¬ p227) ∨ (¬ p237) ∨ (¬ p304) ∨ (¬ p1036) ∨ (¬ p1116) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p788 := by
    exact h5066
  have u9 : (¬ p791) := by
    exact h16213
  rcases h16015 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u8)
  · exact False.elim (u9 q6)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step20531 (p7 p133 p224 p256 p481 p576 p792 p814 p842 p996 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h4535 : p792)
    (h16016 : p7 ∨ p133 ∨ (¬ p224) ∨ (¬ p256) ∨ (¬ p481) ∨ (¬ p576) ∨ (¬ p792) ∨ (¬ p814) ∨ (¬ p842) ∨ (¬ p996)) : (¬ p224) ∨ (¬ p256) ∨ (¬ p481) ∨ (¬ p576) ∨ (¬ p814) ∨ (¬ p842) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p842 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p133) := by
    exact h16157
  have u9 : p792 := by
    exact h4535
  rcases h16016 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step20532 (p7 p14 p172 p480 p656 p840 p1187 : Prop)
    (h16152 : (¬ p7))
    (h16017 : p7 ∨ (¬ p14) ∨ (¬ p172) ∨ (¬ p480) ∨ (¬ p656) ∨ (¬ p840) ∨ (¬ p1187)) : (¬ p14) ∨ (¬ p172) ∨ (¬ p480) ∨ (¬ p656) ∨ (¬ p840) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p480 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p656 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h16017 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20533 (p7 p71 p423 p481 p1187 p1210 p1226 p1237 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16018 : p7 ∨ (¬ p71) ∨ (¬ p423) ∨ (¬ p481) ∨ (¬ p1187) ∨ (¬ p1210) ∨ (¬ p1226) ∨ (¬ p1237) ∨ (¬ p1452)) : (¬ p71) ∨ (¬ p423) ∨ (¬ p481) ∨ (¬ p1187) ∨ (¬ p1210) ∨ (¬ p1226) ∨ (¬ p1237) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h16018 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20534 (p7 p256 p576 p657 p792 p864 p904 p1096 p1136 p1349 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16259 : (¬ p1136))
    (h16019 : p7 ∨ (¬ p256) ∨ (¬ p576) ∨ (¬ p657) ∨ (¬ p792) ∨ (¬ p864) ∨ (¬ p904) ∨ (¬ p1096) ∨ p1136 ∨ (¬ p1349)) : (¬ p256) ∨ (¬ p576) ∨ (¬ p657) ∨ (¬ p864) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1349) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p792 := by
    exact h4535
  have u9 : (¬ p1136) := by
    exact h16259
  rcases h16019 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u9 q8)
  · exact False.elim (q9 u6)

theorem step20535 (p7 p19 p788 p814 p1141 p1255 p1346 p1527 : Prop)
    (h16152 : (¬ p7))
    (h5066 : p788)
    (h16359 : (¬ p1527))
    (h16020 : p7 ∨ (¬ p19) ∨ (¬ p788) ∨ (¬ p814) ∨ (¬ p1141) ∨ (¬ p1255) ∨ (¬ p1346) ∨ p1527) : (¬ p19) ∨ (¬ p814) ∨ (¬ p1141) ∨ (¬ p1255) ∨ (¬ p1346) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p788 := by
    exact h5066
  have u7 : (¬ p1527) := by
    exact h16359
  rcases h16020 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step20536 (p3 p7 p133 p265 p532 p576 p728 p792 p880 p904 p961 p1330 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h4535 : p792)
    (h16021 : (¬ p3) ∨ p7 ∨ p133 ∨ (¬ p265) ∨ (¬ p532) ∨ (¬ p576) ∨ (¬ p728) ∨ (¬ p792) ∨ (¬ p880) ∨ (¬ p904) ∨ (¬ p961) ∨ (¬ p1330)) : (¬ p3) ∨ (¬ p265) ∨ (¬ p532) ∨ (¬ p576) ∨ (¬ p728) ∨ (¬ p880) ∨ (¬ p904) ∨ (¬ p961) ∨ (¬ p1330) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p133) := by
    exact h16157
  have u11 : p792 := by
    exact h4535
  rcases h16021 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u0)
  · exact False.elim (u9 q1)
  · exact False.elim (u10 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step20537 (p7 p256 p430 p576 p792 p814 p1015 : Prop)
    (h16152 : (¬ p7))
    (h16180 : (¬ p430))
    (h4535 : p792)
    (h16022 : p7 ∨ (¬ p256) ∨ p430 ∨ (¬ p576) ∨ (¬ p792) ∨ (¬ p814) ∨ (¬ p1015)) : (¬ p256) ∨ (¬ p576) ∨ (¬ p814) ∨ (¬ p1015) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p430) := by
    exact h16180
  have u6 : p792 := by
    exact h4535
  rcases h16022 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step20538 (p7 p15 p234 p389 p996 p1226 p1237 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16023 : p7 ∨ (¬ p15) ∨ (¬ p234) ∨ (¬ p389) ∨ (¬ p996) ∨ (¬ p1226) ∨ (¬ p1237) ∨ (¬ p1452)) : (¬ p15) ∨ (¬ p234) ∨ (¬ p389) ∨ (¬ p996) ∨ (¬ p1226) ∨ (¬ p1237) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h16023 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20539 (p7 p15 p234 p256 p576 p792 p864 p996 p1136 p1349 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16259 : (¬ p1136))
    (h16024 : p7 ∨ (¬ p15) ∨ (¬ p234) ∨ (¬ p256) ∨ (¬ p576) ∨ (¬ p792) ∨ (¬ p864) ∨ (¬ p996) ∨ p1136 ∨ (¬ p1349)) : (¬ p15) ∨ (¬ p234) ∨ (¬ p256) ∨ (¬ p576) ∨ (¬ p864) ∨ (¬ p996) ∨ (¬ p1349) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p792 := by
    exact h4535
  have u9 : (¬ p1136) := by
    exact h16259
  rcases h16024 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u9 q8)
  · exact False.elim (q9 u6)

theorem step20540 (p7 p8 p435 p682 p728 p996 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16203 : (¬ p682))
    (h6744 : p1135)
    (h16025 : p7 ∨ (¬ p8) ∨ (¬ p435) ∨ p682 ∨ (¬ p728) ∨ (¬ p996) ∨ (¬ p1135)) : (¬ p8) ∨ (¬ p435) ∨ (¬ p728) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p682) := by
    exact h16203
  have u6 : p1135 := by
    exact h6744
  rcases h16025 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step20541 (p7 p106 p225 p349 p434 p734 : Prop)
    (h16152 : (¬ p7))
    (h16026 : p7 ∨ (¬ p106) ∨ (¬ p225) ∨ (¬ p349) ∨ (¬ p434) ∨ (¬ p734)) : (¬ p106) ∨ (¬ p225) ∨ (¬ p349) ∨ (¬ p434) ∨ (¬ p734) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h16026 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20542 (p7 p258 p532 p1084 p1496 p1508 : Prop)
    (h16152 : (¬ p7))
    (h16027 : p7 ∨ (¬ p258) ∨ (¬ p532) ∨ (¬ p1084) ∨ (¬ p1496) ∨ (¬ p1508)) : (¬ p258) ∨ (¬ p532) ∨ (¬ p1084) ∨ (¬ p1496) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h16027 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20543 (p7 p143 p532 p1206 p1496 p1508 : Prop)
    (h16152 : (¬ p7))
    (h16028 : p7 ∨ (¬ p143) ∨ (¬ p532) ∨ (¬ p1206) ∨ (¬ p1496) ∨ (¬ p1508)) : (¬ p143) ∨ (¬ p532) ∨ (¬ p1206) ∨ (¬ p1496) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h16028 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20544 (p3 p7 p16 p71 p544 p728 p1330 p1349 p1489 : Prop)
    (h16152 : (¬ p7))
    (h16029 : (¬ p3) ∨ p7 ∨ (¬ p16) ∨ (¬ p71) ∨ (¬ p544) ∨ (¬ p728) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p1489)) : (¬ p3) ∨ (¬ p16) ∨ (¬ p71) ∨ (¬ p544) ∨ (¬ p728) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h16029 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20545 (p162 p668 p840 p1139 : Prop)
    (h16160 : (¬ p162))
    (h6761 : p1139)
    (h16030 : p162 ∨ p668 ∨ (¬ p840) ∨ (¬ p1139)) : p668 ∨ (¬ p840) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p668) := fun hu => hn (Or.inl hu)
  have u1 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p162) := by
    exact h16160
  have u3 : p1139 := by
    exact h6761
  rcases h16030 with q0 | q1 | q2 | q3
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)

theorem step20546 (p7 p8 p19 p105 p557 p879 p897 : Prop)
    (h16152 : (¬ p7))
    (h16031 : p7 ∨ (¬ p8) ∨ (¬ p19) ∨ (¬ p105) ∨ (¬ p557) ∨ (¬ p879) ∨ (¬ p897)) : (¬ p8) ∨ (¬ p19) ∨ (¬ p105) ∨ (¬ p557) ∨ (¬ p879) ∨ (¬ p897) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p879 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h16031 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20547 (p7 p11 p15 p16 p17 p234 p389 p996 : Prop)
    (h16152 : (¬ p7))
    (h16032 : p7 ∨ (¬ p11) ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p234) ∨ (¬ p389) ∨ (¬ p996)) : (¬ p11) ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p234) ∨ (¬ p389) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h16032 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20548 (p7 p19 p133 p481 p788 p996 p1188 p1287 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h5066 : p788)
    (h16034 : p7 ∨ (¬ p19) ∨ p133 ∨ (¬ p481) ∨ (¬ p788) ∨ (¬ p996) ∨ (¬ p1188) ∨ (¬ p1287)) : (¬ p19) ∨ (¬ p481) ∨ (¬ p996) ∨ (¬ p1188) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p133) := by
    exact h16157
  have u7 : p788 := by
    exact h5066
  rcases h16034 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step20549 (p7 p224 p545 p1002 p1035 p1325 : Prop)
    (h16152 : (¬ p7))
    (h16035 : p7 ∨ (¬ p224) ∨ (¬ p545) ∨ (¬ p1002) ∨ (¬ p1035) ∨ (¬ p1325)) : (¬ p224) ∨ (¬ p545) ∨ (¬ p1002) ∨ (¬ p1035) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1002 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h16035 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20550 (p7 p69 p86 p237 p657 p840 p1004 p1141 : Prop)
    (h16152 : (¬ p7))
    (h16036 : p7 ∨ (¬ p69) ∨ (¬ p86) ∨ (¬ p237) ∨ (¬ p657) ∨ (¬ p840) ∨ (¬ p1004) ∨ (¬ p1141)) : (¬ p69) ∨ (¬ p86) ∨ (¬ p237) ∨ (¬ p657) ∨ (¬ p840) ∨ (¬ p1004) ∨ (¬ p1141) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h16036 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20551 (p7 p14 p64 p86 p226 p256 p288 p325 p342 p1187 : Prop)
    (h16152 : (¬ p7))
    (h16037 : p7 ∨ (¬ p14) ∨ (¬ p64) ∨ (¬ p86) ∨ (¬ p226) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p325) ∨ (¬ p342) ∨ (¬ p1187)) : (¬ p14) ∨ (¬ p64) ∨ (¬ p86) ∨ (¬ p226) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p325) ∨ (¬ p342) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p342 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h16037 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20552 (p7 p139 p323 p364 p406 p514 p858 : Prop)
    (h16152 : (¬ p7))
    (h16038 : p7 ∨ (¬ p139) ∨ (¬ p323) ∨ (¬ p364) ∨ (¬ p406) ∨ (¬ p514) ∨ (¬ p858)) : (¬ p139) ∨ (¬ p323) ∨ (¬ p364) ∨ (¬ p406) ∨ (¬ p514) ∨ (¬ p858) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p139 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p514 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h16038 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20553 (p7 p69 p86 p229 p669 p789 p790 p1036 : Prop)
    (h16152 : (¬ p7))
    (h16039 : p7 ∨ (¬ p69) ∨ (¬ p86) ∨ (¬ p229) ∨ (¬ p669) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1036)) : (¬ p69) ∨ (¬ p86) ∨ (¬ p229) ∨ (¬ p669) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1036) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h16039 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20554 (p7 p139 p256 p323 p515 p814 : Prop)
    (h16152 : (¬ p7))
    (h16041 : p7 ∨ (¬ p139) ∨ (¬ p256) ∨ (¬ p323) ∨ (¬ p515) ∨ (¬ p814)) : (¬ p139) ∨ (¬ p256) ∨ (¬ p323) ∨ (¬ p515) ∨ (¬ p814) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p139 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p515 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h16041 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20555 (p7 p69 p229 p230 p406 p816 p940 p985 p1184 p1333 p1393 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h7053 : p1184)
    (h16042 : p7 ∨ (¬ p69) ∨ (¬ p229) ∨ p230 ∨ (¬ p406) ∨ (¬ p816) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1184) ∨ (¬ p1333) ∨ (¬ p1393)) : (¬ p69) ∨ (¬ p229) ∨ (¬ p406) ∨ (¬ p816) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1333) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p230) := by
    exact h16165
  have u10 : p1184 := by
    exact h7053
  rcases h16042 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u9 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step20556 (p7 p10 p69 p229 p280 p669 p1035 p1036 p1184 p1212 p1325 : Prop)
    (h16152 : (¬ p7))
    (h16173 : (¬ p280))
    (h7053 : p1184)
    (h16043 : p7 ∨ (¬ p10) ∨ (¬ p69) ∨ (¬ p229) ∨ p280 ∨ (¬ p669) ∨ (¬ p1035) ∨ (¬ p1036) ∨ (¬ p1184) ∨ (¬ p1212) ∨ (¬ p1325)) : (¬ p10) ∨ (¬ p69) ∨ (¬ p229) ∨ (¬ p669) ∨ (¬ p1035) ∨ (¬ p1036) ∨ (¬ p1212) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1212 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p280) := by
    exact h16173
  have u10 : p1184 := by
    exact h7053
  rcases h16043 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u9 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step20557 (p7 p64 p206 p230 p304 p456 p633 p814 p1184 p1346 p1393 p1490 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h7053 : p1184)
    (h16044 : p7 ∨ (¬ p64) ∨ (¬ p206) ∨ p230 ∨ (¬ p304) ∨ (¬ p456) ∨ (¬ p633) ∨ (¬ p814) ∨ (¬ p1184) ∨ (¬ p1346) ∨ (¬ p1393) ∨ (¬ p1490)) : (¬ p64) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p456) ∨ (¬ p633) ∨ (¬ p814) ∨ (¬ p1346) ∨ (¬ p1393) ∨ (¬ p1490) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1490 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p230) := by
    exact h16165
  have u11 : p1184 := by
    exact h7053
  rcases h16044 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u10 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u11)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step20558 (p7 p14 p226 p230 p303 p331 p406 p519 p581 p659 p816 p1187 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h3753 : p659)
    (h16045 : p7 ∨ (¬ p14) ∨ (¬ p226) ∨ p230 ∨ (¬ p303) ∨ (¬ p331) ∨ (¬ p406) ∨ (¬ p519) ∨ (¬ p581) ∨ (¬ p659) ∨ (¬ p816) ∨ (¬ p1187)) : (¬ p14) ∨ (¬ p226) ∨ (¬ p303) ∨ (¬ p331) ∨ (¬ p406) ∨ (¬ p519) ∨ (¬ p581) ∨ (¬ p816) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p226 := by
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
  have u4 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p519 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p230) := by
    exact h16165
  have u11 : p659 := by
    exact h3753
  rcases h16045 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u10 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u11)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step20559 (p3 p6 p7 p257 p346 p544 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h6478 : p1075)
    (h16046 : (¬ p3) ∨ (¬ p6) ∨ p7 ∨ p257 ∨ (¬ p346) ∨ (¬ p544) ∨ (¬ p1075)) : (¬ p3) ∨ (¬ p6) ∨ (¬ p346) ∨ (¬ p544) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p257) := by
    exact h16170
  have u6 : p1075 := by
    exact h6478
  rcases h16046 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u4 q2)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step20560 (p7 p45 p192 p544 p556 p710 p792 p1036 p1181 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16272 : (¬ p1181))
    (h16049 : p7 ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p544) ∨ (¬ p556) ∨ (¬ p710) ∨ (¬ p792) ∨ (¬ p1036) ∨ p1181) : (¬ p45) ∨ (¬ p192) ∨ (¬ p544) ∨ (¬ p556) ∨ (¬ p710) ∨ (¬ p1036) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : p792 := by
    exact h4535
  have u8 : (¬ p1181) := by
    exact h16272
  rcases h16049 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u5)
  · exact False.elim (u8 q8)

theorem step20561 (p2 p7 p45 p90 p192 p237 p419 p665 p1116 : Prop)
    (h16152 : (¬ p7))
    (h16050 : (¬ p2) ∨ p7 ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p192) ∨ (¬ p237) ∨ (¬ p419) ∨ (¬ p665) ∨ (¬ p1116)) : (¬ p2) ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p192) ∨ (¬ p237) ∨ (¬ p419) ∨ (¬ p665) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h16050 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20562 (p7 p41 p42 p227 p456 p498 p544 p575 p710 p1036 p1103 p1181 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16272 : (¬ p1181))
    (h16051 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p227) ∨ (¬ p456) ∨ (¬ p498) ∨ (¬ p544) ∨ (¬ p575) ∨ (¬ p710) ∨ (¬ p1036) ∨ (¬ p1103) ∨ p1181) : (¬ p41) ∨ (¬ p227) ∨ (¬ p456) ∨ (¬ p498) ∨ (¬ p544) ∨ (¬ p575) ∨ (¬ p710) ∨ (¬ p1036) ∨ (¬ p1103) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p575 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p42 := by
    exact h132
  have u11 : (¬ p1181) := by
    exact h16272
  rcases h16051 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u8)
  · exact False.elim (u11 q11)

theorem step20563 (p7 p455 p499 p544 p710 p1036 p1081 p1103 : Prop)
    (h16152 : (¬ p7))
    (h16052 : p7 ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p544) ∨ (¬ p710) ∨ (¬ p1036) ∨ (¬ p1081) ∨ (¬ p1103)) : (¬ p455) ∨ (¬ p499) ∨ (¬ p544) ∨ (¬ p710) ∨ (¬ p1036) ∨ (¬ p1081) ∨ (¬ p1103) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h16052 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20564 (p5 p7 p224 p225 p226 p228 p455 p499 : Prop)
    (h16152 : (¬ p7))
    (h16053 : (¬ p5) ∨ p7 ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p228) ∨ (¬ p455) ∨ (¬ p499)) : (¬ p5) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p228) ∨ (¬ p455) ∨ (¬ p499) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h16053 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20565 (p5 p7 p41 p42 p224 p225 p226 p227 p302 p456 p498 p575 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16285 : (¬ p302))
    (h16054 : (¬ p5) ∨ p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p227) ∨ p302 ∨ (¬ p456) ∨ (¬ p498) ∨ (¬ p575)) : (¬ p5) ∨ (¬ p41) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p227) ∨ (¬ p456) ∨ (¬ p498) ∨ (¬ p575) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p575 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p42 := by
    exact h132
  have u11 : (¬ p302) := by
    exact h16285
  rcases h16054 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u0)
  · exact False.elim (u9 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u11 q8)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step20566 (p6 p7 p45 p90 p192 p389 p789 p790 p1206 : Prop)
    (h16152 : (¬ p7))
    (h16055 : (¬ p6) ∨ p7 ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p192) ∨ (¬ p389) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1206)) : (¬ p6) ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p192) ∨ (¬ p389) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h16055 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20568 (p7 p237 p789 p791 p918 p1135 p1393 : Prop)
    (h16152 : (¬ p7))
    (h16213 : (¬ p791))
    (h6744 : p1135)
    (h16057 : p7 ∨ (¬ p237) ∨ (¬ p789) ∨ p791 ∨ (¬ p918) ∨ (¬ p1135) ∨ (¬ p1393)) : (¬ p237) ∨ (¬ p789) ∨ (¬ p918) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p791) := by
    exact h16213
  have u6 : p1135 := by
    exact h6744
  rcases h16057 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step20569 (p7 p24 p63 p125 p210 p431 p438 p633 p789 p1075 p1136 p1393 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16259 : (¬ p1136))
    (h16059 : p7 ∨ p24 ∨ (¬ p63) ∨ (¬ p125) ∨ (¬ p210) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p633) ∨ (¬ p789) ∨ (¬ p1075) ∨ p1136 ∨ (¬ p1393)) : p24 ∨ (¬ p63) ∨ (¬ p125) ∨ (¬ p210) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p633) ∨ (¬ p789) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p24) := fun hu => hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p1075 := by
    exact h6478
  have u11 : (¬ p1136) := by
    exact h16259
  rcases h16059 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u10)
  · exact False.elim (u11 q10)
  · exact False.elim (q11 u8)

theorem step20570 (p7 p18 p127 p128 p225 p226 p426 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16178 : (¬ p426))
    (h16060 : p7 ∨ (¬ p18) ∨ (¬ p127) ∨ (¬ p128) ∨ (¬ p225) ∨ (¬ p226) ∨ p426) : (¬ p18) ∨ (¬ p127) ∨ (¬ p225) ∨ (¬ p226) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p128 := by
    exact h653
  have u6 : (¬ p426) := by
    exact h16178
  rcases h16060 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step20571 (p3 p7 p18 p72 p210 p304 p346 p668 p880 p1095 : Prop)
    (h16152 : (¬ p7))
    (h16061 : (¬ p3) ∨ p7 ∨ (¬ p18) ∨ (¬ p72) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p668) ∨ (¬ p880) ∨ (¬ p1095)) : (¬ p3) ∨ (¬ p18) ∨ (¬ p72) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p668) ∨ (¬ p880) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h16061 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (u9 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20572 (p7 p18 p72 p103 p348 p431 p438 p481 p560 p710 p789 p1189 p1391 : Prop)
    (h16152 : (¬ p7))
    (h16062 : p7 ∨ (¬ p18) ∨ (¬ p72) ∨ (¬ p103) ∨ (¬ p348) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p481) ∨ (¬ p560) ∨ (¬ p710) ∨ (¬ p789) ∨ (¬ p1189) ∨ (¬ p1391)) : (¬ p18) ∨ (¬ p72) ∨ (¬ p103) ∨ (¬ p348) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p481) ∨ (¬ p560) ∨ (¬ p710) ∨ (¬ p789) ∨ (¬ p1189) ∨ (¬ p1391) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p1391 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))
  have u12 : (¬ p7) := by
    exact h16152
  rcases h16062 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (u12 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)
  · exact False.elim (q10 u9)
  · exact False.elim (q11 u10)
  · exact False.elim (q12 u11)

theorem step20573 (p7 p285 p344 p656 p687 p834 p1015 : Prop)
    (h16152 : (¬ p7))
    (h16063 : p7 ∨ (¬ p285) ∨ (¬ p344) ∨ (¬ p656) ∨ (¬ p687) ∨ (¬ p834) ∨ (¬ p1015)) : (¬ p285) ∨ (¬ p344) ∨ (¬ p656) ∨ (¬ p687) ∨ (¬ p834) ∨ (¬ p1015) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p285 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p656 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p834 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h16063 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20574 (p7 p104 p121 p127 p226 p1084 : Prop)
    (h16152 : (¬ p7))
    (h16064 : p7 ∨ (¬ p104) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p226) ∨ (¬ p1084)) : (¬ p104) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p226) ∨ (¬ p1084) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h16064 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20575 (p7 p18 p46 p140 p189 p256 : Prop)
    (h16152 : (¬ p7))
    (h16065 : p7 ∨ (¬ p18) ∨ (¬ p46) ∨ (¬ p140) ∨ (¬ p189) ∨ (¬ p256)) : (¬ p18) ∨ (¬ p46) ∨ (¬ p140) ∨ (¬ p189) ∨ (¬ p256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p46 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h16065 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20577 (p7 p18 p72 p125 p210 p224 p351 p481 p996 : Prop)
    (h16152 : (¬ p7))
    (h16067 : p7 ∨ (¬ p18) ∨ (¬ p72) ∨ (¬ p125) ∨ (¬ p210) ∨ (¬ p224) ∨ (¬ p351) ∨ (¬ p481) ∨ (¬ p996)) : (¬ p18) ∨ (¬ p72) ∨ (¬ p125) ∨ (¬ p210) ∨ (¬ p224) ∨ (¬ p351) ∨ (¬ p481) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h16067 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20578 (p7 p8 p9 p11 p13 p16 p17 p897 p1095 : Prop)
    (h16152 : (¬ p7))
    (h16068 : p7 ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p11) ∨ (¬ p13) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p897) ∨ (¬ p1095)) : (¬ p8) ∨ (¬ p9) ∨ (¬ p11) ∨ (¬ p13) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p897) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p13 := by
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
  have u6 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h16068 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20579 (p7 p226 p882 p1041 p1074 p1140 : Prop)
    (h16152 : (¬ p7))
    (h16069 : p7 ∨ (¬ p226) ∨ (¬ p882) ∨ (¬ p1041) ∨ (¬ p1074) ∨ (¬ p1140)) : (¬ p226) ∨ (¬ p882) ∨ (¬ p1041) ∨ (¬ p1074) ∨ (¬ p1140) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p882 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1041 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h16069 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20580 (p7 p18 p210 p258 p262 p423 p1084 p1211 : Prop)
    (h16152 : (¬ p7))
    (h16070 : p7 ∨ (¬ p18) ∨ (¬ p210) ∨ (¬ p258) ∨ (¬ p262) ∨ (¬ p423) ∨ (¬ p1084) ∨ (¬ p1211)) : (¬ p18) ∨ (¬ p210) ∨ (¬ p258) ∨ (¬ p262) ∨ (¬ p423) ∨ (¬ p1084) ∨ (¬ p1211) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h16070 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20581 (p3 p7 p72 p728 p880 p904 p1141 p1167 p1226 p1330 : Prop)
    (h16152 : (¬ p7))
    (h16071 : (¬ p3) ∨ p7 ∨ (¬ p72) ∨ (¬ p728) ∨ (¬ p880) ∨ (¬ p904) ∨ (¬ p1141) ∨ (¬ p1167) ∨ (¬ p1226) ∨ (¬ p1330)) : (¬ p3) ∨ (¬ p72) ∨ (¬ p728) ∨ (¬ p880) ∨ (¬ p904) ∨ (¬ p1141) ∨ (¬ p1167) ∨ (¬ p1226) ∨ (¬ p1330) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h16071 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (u9 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20582 (p3 p7 p72 p435 p657 p680 p682 p687 p880 p904 p1135 p1187 : Prop)
    (h16152 : (¬ p7))
    (h16203 : (¬ p682))
    (h6744 : p1135)
    (h16072 : (¬ p3) ∨ p7 ∨ (¬ p72) ∨ (¬ p435) ∨ (¬ p657) ∨ (¬ p680) ∨ p682 ∨ (¬ p687) ∨ (¬ p880) ∨ (¬ p904) ∨ (¬ p1135) ∨ (¬ p1187)) : (¬ p3) ∨ (¬ p72) ∨ (¬ p435) ∨ (¬ p657) ∨ (¬ p680) ∨ (¬ p687) ∨ (¬ p880) ∨ (¬ p904) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p682) := by
    exact h16203
  have u11 : p1135 := by
    exact h6744
  rcases h16072 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u0)
  · exact False.elim (u9 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u10 q6)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u11)
  · exact False.elim (q11 u8)

theorem step20583 (p7 p18 p127 p133 p234 p996 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h6744 : p1135)
    (h16073 : p7 ∨ (¬ p18) ∨ (¬ p127) ∨ p133 ∨ (¬ p234) ∨ (¬ p996) ∨ (¬ p1135)) : (¬ p18) ∨ (¬ p127) ∨ (¬ p234) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p133) := by
    exact h16157
  have u6 : p1135 := by
    exact h6744
  rcases h16073 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step20584 (p7 p21 p127 p133 p241 p434 p601 p792 p918 p980 p1055 p1330 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h4535 : p792)
    (h16074 : p7 ∨ (¬ p21) ∨ (¬ p127) ∨ p133 ∨ (¬ p241) ∨ (¬ p434) ∨ (¬ p601) ∨ (¬ p792) ∨ (¬ p918) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1330)) : (¬ p21) ∨ (¬ p127) ∨ (¬ p241) ∨ (¬ p434) ∨ (¬ p601) ∨ (¬ p918) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1330) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p133) := by
    exact h16157
  have u11 : p792 := by
    exact h4535
  rcases h16074 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u10 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step20585 (p7 p133 p237 p423 p481 p792 p918 p1187 p1258 p1349 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h4535 : p792)
    (h16075 : p7 ∨ p133 ∨ (¬ p237) ∨ (¬ p423) ∨ (¬ p481) ∨ (¬ p792) ∨ (¬ p918) ∨ (¬ p1187) ∨ (¬ p1258) ∨ (¬ p1349)) : (¬ p237) ∨ (¬ p423) ∨ (¬ p481) ∨ (¬ p918) ∨ (¬ p1187) ∨ (¬ p1258) ∨ (¬ p1349) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p133) := by
    exact h16157
  have u9 : p792 := by
    exact h4535
  rcases h16075 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step20586 (p7 p18 p127 p133 p241 p423 p792 p918 p983 p1040 p1056 p1226 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h4535 : p792)
    (h16076 : p7 ∨ (¬ p18) ∨ (¬ p127) ∨ p133 ∨ (¬ p241) ∨ (¬ p423) ∨ (¬ p792) ∨ (¬ p918) ∨ (¬ p983) ∨ (¬ p1040) ∨ (¬ p1056) ∨ (¬ p1226)) : (¬ p18) ∨ (¬ p127) ∨ (¬ p241) ∨ (¬ p423) ∨ (¬ p918) ∨ (¬ p983) ∨ (¬ p1040) ∨ (¬ p1056) ∨ (¬ p1226) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1040 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1056 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p133) := by
    exact h16157
  have u11 : p792 := by
    exact h4535
  rcases h16076 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u10 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step20587 (p7 p157 p160 p344 p686 p710 p1135 p1325 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h6744 : p1135)
    (h16077 : p7 ∨ (¬ p157) ∨ (¬ p160) ∨ (¬ p344) ∨ p686 ∨ (¬ p710) ∨ (¬ p1135) ∨ (¬ p1325)) : (¬ p157) ∨ (¬ p160) ∨ (¬ p344) ∨ (¬ p710) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p157 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p686) := by
    exact h16205
  have u7 : p1135 := by
    exact h6744
  rcases h16077 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step20588 (p7 p13 p18 p128 p210 p344 p686 p710 p959 p1095 p1102 p1226 p1452 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16205 : (¬ p686))
    (h16078 : p7 ∨ (¬ p13) ∨ (¬ p18) ∨ (¬ p128) ∨ (¬ p210) ∨ (¬ p344) ∨ p686 ∨ (¬ p710) ∨ (¬ p959) ∨ (¬ p1095) ∨ (¬ p1102) ∨ (¬ p1226) ∨ (¬ p1452)) : (¬ p13) ∨ (¬ p18) ∨ (¬ p210) ∨ (¬ p344) ∨ (¬ p710) ∨ (¬ p959) ∨ (¬ p1095) ∨ (¬ p1102) ∨ (¬ p1226) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p959 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : p128 := by
    exact h653
  have u12 : (¬ p686) := by
    exact h16205
  rcases h16078 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u12 q6)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)
  · exact False.elim (q12 u9)

theorem step20589 (p7 p18 p71 p127 p616 p1190 : Prop)
    (h16152 : (¬ p7))
    (h16079 : p7 ∨ (¬ p18) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p616) ∨ (¬ p1190)) : (¬ p18) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p616) ∨ (¬ p1190) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h16079 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20590 (p7 p18 p43 p127 p792 p980 p1044 p1136 p1159 p1225 p1229 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16259 : (¬ p1136))
    (h16080 : p7 ∨ (¬ p18) ∨ (¬ p43) ∨ (¬ p127) ∨ (¬ p792) ∨ (¬ p980) ∨ (¬ p1044) ∨ p1136 ∨ (¬ p1159) ∨ (¬ p1225) ∨ (¬ p1229)) : (¬ p18) ∨ (¬ p43) ∨ (¬ p127) ∨ (¬ p980) ∨ (¬ p1044) ∨ (¬ p1159) ∨ (¬ p1225) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p792 := by
    exact h4535
  have u10 : (¬ p1136) := by
    exact h16259
  rcases h16080 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u10 q7)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step20591 (p7 p16 p17 p983 p1095 p1096 p1454 p1644 : Prop)
    (h16152 : (¬ p7))
    (h16082 : p7 ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p983) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1454) ∨ (¬ p1644)) : (¬ p16) ∨ (¬ p17) ∨ (¬ p983) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1454) ∨ (¬ p1644) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1454 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h16082 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20592 (p7 p45 p192 p226 p455 p499 p792 p940 p985 p1136 p1452 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16259 : (¬ p1136))
    (h16083 : p7 ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p226) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p792) ∨ (¬ p940) ∨ (¬ p985) ∨ p1136 ∨ (¬ p1452)) : (¬ p45) ∨ (¬ p192) ∨ (¬ p226) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p792 := by
    exact h4535
  have u10 : (¬ p1136) := by
    exact h16259
  rcases h16083 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (u10 q9)
  · exact False.elim (q10 u7)

theorem step20594 (p7 p342 p364 p406 p594 p633 p1287 : Prop)
    (h16152 : (¬ p7))
    (h16085 : p7 ∨ (¬ p342) ∨ (¬ p364) ∨ (¬ p406) ∨ (¬ p594) ∨ (¬ p633) ∨ (¬ p1287)) : (¬ p342) ∨ (¬ p364) ∨ (¬ p406) ∨ (¬ p594) ∨ (¬ p633) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p342 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p594 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h16085 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20595 (p5 p7 p226 p595 p940 p985 p1286 p1333 : Prop)
    (h16152 : (¬ p7))
    (h16086 : (¬ p5) ∨ p7 ∨ (¬ p226) ∨ (¬ p595) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1286) ∨ (¬ p1333)) : (¬ p5) ∨ (¬ p226) ∨ (¬ p595) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1286) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h16086 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20596 (p7 p1002 p1035 p1191 p1287 p1325 : Prop)
    (h16152 : (¬ p7))
    (h16087 : p7 ∨ (¬ p1002) ∨ (¬ p1035) ∨ (¬ p1191) ∨ (¬ p1287) ∨ (¬ p1325)) : (¬ p1002) ∨ (¬ p1035) ∨ (¬ p1191) ∨ (¬ p1287) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1002 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h16087 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20597 (p5 p7 p89 p226 p669 p1036 p1325 p1346 p1508 : Prop)
    (h16152 : (¬ p7))
    (h16088 : (¬ p5) ∨ p7 ∨ (¬ p89) ∨ (¬ p226) ∨ (¬ p669) ∨ (¬ p1036) ∨ (¬ p1325) ∨ (¬ p1346) ∨ (¬ p1508)) : (¬ p5) ∨ (¬ p89) ∨ (¬ p226) ∨ (¬ p669) ∨ (¬ p1036) ∨ (¬ p1325) ∨ (¬ p1346) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h16088 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20598 (p7 p18 p89 p128 p210 p304 p790 p1076 p1120 p1136 p1273 p1385 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16259 : (¬ p1136))
    (h16089 : p7 ∨ (¬ p18) ∨ (¬ p89) ∨ (¬ p128) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p790) ∨ (¬ p1076) ∨ (¬ p1120) ∨ p1136 ∨ (¬ p1273) ∨ (¬ p1385)) : (¬ p18) ∨ (¬ p89) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p790) ∨ (¬ p1076) ∨ (¬ p1120) ∨ (¬ p1273) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p128 := by
    exact h653
  have u11 : (¬ p1136) := by
    exact h16259
  rcases h16089 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (u11 q9)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step20599 (p7 p18 p128 p210 p304 p669 p1076 p1136 p1225 p1229 p1325 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16259 : (¬ p1136))
    (h16090 : p7 ∨ (¬ p18) ∨ (¬ p128) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p669) ∨ (¬ p1076) ∨ p1136 ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1325)) : (¬ p18) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p669) ∨ (¬ p1076) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p128 := by
    exact h653
  have u10 : (¬ p1136) := by
    exact h16259
  rcases h16090 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u10 q7)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step20600 (p7 p89 p132 p159 p161 p581 p1136 p1346 p1508 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16259 : (¬ p1136))
    (h16091 : p7 ∨ (¬ p89) ∨ (¬ p132) ∨ (¬ p159) ∨ (¬ p161) ∨ (¬ p581) ∨ p1136 ∨ (¬ p1346) ∨ (¬ p1508)) : (¬ p89) ∨ (¬ p159) ∨ (¬ p161) ∨ (¬ p581) ∨ (¬ p1346) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : p132 := by
    exact h786
  have u8 : (¬ p1136) := by
    exact h16259
  rcases h16091 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u8 q6)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step20602 (p7 p41 p42 p406 p853 p858 p1385 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16216 : (¬ p853))
    (h16093 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p406) ∨ p853 ∨ (¬ p858) ∨ (¬ p1385)) : (¬ p41) ∨ (¬ p406) ∨ (¬ p858) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p42 := by
    exact h132
  have u6 : (¬ p853) := by
    exact h16216
  rcases h16093 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step20603 (p7 p256 p342 p515 p574 p633 p814 : Prop)
    (h16152 : (¬ p7))
    (h16094 : p7 ∨ (¬ p256) ∨ (¬ p342) ∨ (¬ p515) ∨ (¬ p574) ∨ (¬ p633) ∨ (¬ p814)) : (¬ p256) ∨ (¬ p342) ∨ (¬ p515) ∨ (¬ p574) ∨ (¬ p633) ∨ (¬ p814) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p342 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p515 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p574 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h16094 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20604 (p5 p7 p10 p41 p42 p102 p206 p280 p304 p406 p620 p1287 p1387 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16173 : (¬ p280))
    (h16095 : (¬ p5) ∨ p7 ∨ (¬ p10) ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p102) ∨ (¬ p206) ∨ p280 ∨ (¬ p304) ∨ (¬ p406) ∨ (¬ p620) ∨ (¬ p1287) ∨ (¬ p1387)) : (¬ p5) ∨ (¬ p10) ∨ (¬ p41) ∨ (¬ p102) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p406) ∨ (¬ p620) ∨ (¬ p1287) ∨ (¬ p1387) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
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
  have u3 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p620 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : p42 := by
    exact h132
  have u12 : (¬ p280) := by
    exact h16173
  rcases h16095 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (q0 u0)
  · exact False.elim (u10 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u12 q7)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)
  · exact False.elim (q12 u9)

theorem step20605 (p7 p102 p139 p283 p756 p1584 : Prop)
    (h16152 : (¬ p7))
    (h16096 : p7 ∨ (¬ p102) ∨ (¬ p139) ∨ (¬ p283) ∨ (¬ p756) ∨ (¬ p1584)) : (¬ p102) ∨ (¬ p139) ∨ (¬ p283) ∨ (¬ p756) ∨ (¬ p1584) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p139 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h16096 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20606 (p7 p63 p789 p1004 p1035 p1226 p1237 p1393 : Prop)
    (h16152 : (¬ p7))
    (h16098 : p7 ∨ (¬ p63) ∨ (¬ p789) ∨ (¬ p1004) ∨ (¬ p1035) ∨ (¬ p1226) ∨ (¬ p1237) ∨ (¬ p1393)) : (¬ p63) ∨ (¬ p789) ∨ (¬ p1004) ∨ (¬ p1035) ∨ (¬ p1226) ∨ (¬ p1237) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h16098 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20607 (p7 p41 p42 p241 p344 p686 p710 p918 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16205 : (¬ p686))
    (h16099 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p241) ∨ (¬ p344) ∨ p686 ∨ (¬ p710) ∨ (¬ p918)) : (¬ p41) ∨ (¬ p241) ∨ (¬ p344) ∨ (¬ p710) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p686) := by
    exact h16205
  rcases h16099 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u7 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step20608 (p7 p168 p406 p544 p656 p834 p858 : Prop)
    (h16152 : (¬ p7))
    (h16100 : p7 ∨ (¬ p168) ∨ (¬ p406) ∨ (¬ p544) ∨ (¬ p656) ∨ (¬ p834) ∨ (¬ p858)) : (¬ p168) ∨ (¬ p406) ∨ (¬ p544) ∨ (¬ p656) ∨ (¬ p834) ∨ (¬ p858) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p168 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p656 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p834 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h16100 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20609 (p7 p10 p102 p267 p304 p406 p517 p820 p858 : Prop)
    (h16152 : (¬ p7))
    (h16101 : p7 ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p267) ∨ (¬ p304) ∨ (¬ p406) ∨ (¬ p517) ∨ (¬ p820) ∨ (¬ p858)) : (¬ p10) ∨ (¬ p102) ∨ (¬ p267) ∨ (¬ p304) ∨ (¬ p406) ∨ (¬ p517) ∨ (¬ p820) ∨ (¬ p858) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p267 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p517 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p820 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h16101 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20610 (p5 p7 p102 p206 p304 p389 p595 p1206 p1286 : Prop)
    (h16152 : (¬ p7))
    (h16102 : (¬ p5) ∨ p7 ∨ (¬ p102) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p389) ∨ (¬ p595) ∨ (¬ p1206) ∨ (¬ p1286)) : (¬ p5) ∨ (¬ p102) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p389) ∨ (¬ p595) ∨ (¬ p1206) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h16102 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20611 (p7 p41 p138 p262 p368 p406 p1287 p1387 : Prop)
    (h16152 : (¬ p7))
    (h16103 : p7 ∨ (¬ p41) ∨ (¬ p138) ∨ (¬ p262) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p1287) ∨ (¬ p1387)) : (¬ p41) ∨ (¬ p138) ∨ (¬ p262) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p1287) ∨ (¬ p1387) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h16103 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20612 (p7 p41 p42 p1035 p1226 p1249 p1352 p1484 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16345 : (¬ p1484))
    (h16104 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p1035) ∨ (¬ p1226) ∨ (¬ p1249) ∨ (¬ p1352) ∨ p1484) : (¬ p41) ∨ (¬ p1035) ∨ (¬ p1226) ∨ (¬ p1249) ∨ (¬ p1352) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1352 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p1484) := by
    exact h16345
  rcases h16104 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step20613 (p7 p41 p42 p125 p257 p265 p323 p576 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16170 : (¬ p257))
    (h16105 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p125) ∨ p257 ∨ (¬ p265) ∨ (¬ p323) ∨ (¬ p576)) : (¬ p41) ∨ (¬ p125) ∨ (¬ p265) ∨ (¬ p323) ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p257) := by
    exact h16170
  rcases h16105 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step20614 (p7 p139 p323 p364 p581 p819 p1385 : Prop)
    (h16152 : (¬ p7))
    (h16106 : p7 ∨ (¬ p139) ∨ (¬ p323) ∨ (¬ p364) ∨ (¬ p581) ∨ (¬ p819) ∨ (¬ p1385)) : (¬ p139) ∨ (¬ p323) ∨ (¬ p364) ∨ (¬ p581) ∨ (¬ p819) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p139 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p819 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h16106 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20615 (p7 p89 p102 p139 p304 p500 p581 p790 p1385 : Prop)
    (h16152 : (¬ p7))
    (h16108 : p7 ∨ (¬ p89) ∨ (¬ p102) ∨ (¬ p139) ∨ (¬ p304) ∨ (¬ p500) ∨ (¬ p581) ∨ (¬ p790) ∨ (¬ p1385)) : (¬ p89) ∨ (¬ p102) ∨ (¬ p139) ∨ (¬ p304) ∨ (¬ p500) ∨ (¬ p581) ∨ (¬ p790) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p139 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h16108 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20616 (p7 p41 p63 p1001 p1136 p1256 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16259 : (¬ p1136))
    (h8348 : p1386)
    (h16109 : p7 ∨ (¬ p41) ∨ (¬ p63) ∨ (¬ p1001) ∨ p1136 ∨ (¬ p1256) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p41) ∨ (¬ p63) ∨ (¬ p1001) ∨ (¬ p1256) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1001 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p1136) := by
    exact h16259
  have u7 : p1386 := by
    exact h8348
  rcases h16109 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step20617 (p7 p288 p342 p364 p406 p514 p858 : Prop)
    (h16152 : (¬ p7))
    (h16110 : p7 ∨ (¬ p288) ∨ (¬ p342) ∨ (¬ p364) ∨ (¬ p406) ∨ (¬ p514) ∨ (¬ p858)) : (¬ p288) ∨ (¬ p342) ∨ (¬ p364) ∨ (¬ p406) ∨ (¬ p514) ∨ (¬ p858) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p342 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p514 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h16110 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20618 (p7 p45 p90 p102 p192 p206 p237 p257 p304 p657 p904 p923 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h6744 : p1135)
    (h16112 : p7 ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p102) ∨ (¬ p192) ∨ (¬ p206) ∨ (¬ p237) ∨ p257 ∨ (¬ p304) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p923) ∨ (¬ p1135)) : (¬ p45) ∨ (¬ p90) ∨ (¬ p102) ∨ (¬ p192) ∨ (¬ p206) ∨ (¬ p237) ∨ (¬ p304) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p923) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p923 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : (¬ p257) := by
    exact h16170
  have u12 : p1135 := by
    exact h6744
  rcases h16112 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u11 q7)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u8)
  · exact False.elim (q11 u9)
  · exact False.elim (q12 u12)

theorem step20619 (p6 p7 p142 p188 p224 p325 p351 p406 p796 p817 : Prop)
    (h16152 : (¬ p7))
    (h16113 : (¬ p6) ∨ p7 ∨ (¬ p142) ∨ (¬ p188) ∨ (¬ p224) ∨ (¬ p325) ∨ (¬ p351) ∨ (¬ p406) ∨ (¬ p796) ∨ (¬ p817)) : (¬ p6) ∨ (¬ p142) ∨ (¬ p188) ∨ (¬ p224) ∨ (¬ p325) ∨ (¬ p351) ∨ (¬ p406) ∨ (¬ p796) ∨ (¬ p817) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p817 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h16113 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (u9 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step20620 (p6 p7 p10 p191 p224 p351 p406 p424 p476 : Prop)
    (h16152 : (¬ p7))
    (h16116 : (¬ p6) ∨ p7 ∨ (¬ p10) ∨ (¬ p191) ∨ (¬ p224) ∨ (¬ p351) ∨ (¬ p406) ∨ (¬ p424) ∨ (¬ p476)) : (¬ p6) ∨ (¬ p10) ∨ (¬ p191) ∨ (¬ p224) ∨ (¬ p351) ∨ (¬ p406) ∨ (¬ p424) ∨ (¬ p476) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p476 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h16116 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20623 (p7 p18 p63 p127 p128 p789 p1004 p1136 p1159 p1393 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16259 : (¬ p1136))
    (h16119 : p7 ∨ (¬ p18) ∨ (¬ p63) ∨ (¬ p127) ∨ (¬ p128) ∨ (¬ p789) ∨ (¬ p1004) ∨ p1136 ∨ (¬ p1159) ∨ (¬ p1393)) : (¬ p18) ∨ (¬ p63) ∨ (¬ p127) ∨ (¬ p789) ∨ (¬ p1004) ∨ (¬ p1159) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p128 := by
    exact h653
  have u9 : (¬ p1136) := by
    exact h16259
  rcases h16119 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u9 q7)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step20624 (p7 p237 p791 p918 p1273 p1386 p1508 : Prop)
    (h16152 : (¬ p7))
    (h16213 : (¬ p791))
    (h8348 : p1386)
    (h16120 : p7 ∨ (¬ p237) ∨ p791 ∨ (¬ p918) ∨ (¬ p1273) ∨ (¬ p1386) ∨ (¬ p1508)) : (¬ p237) ∨ (¬ p918) ∨ (¬ p1273) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p791) := by
    exact h16213
  have u6 : p1386 := by
    exact h8348
  rcases h16120 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step20625 (p7 p18 p127 p128 p325 p349 p477 p686 p690 p1366 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16205 : (¬ p686))
    (h16121 : p7 ∨ (¬ p18) ∨ (¬ p127) ∨ (¬ p128) ∨ (¬ p325) ∨ (¬ p349) ∨ (¬ p477) ∨ p686 ∨ (¬ p690) ∨ (¬ p1366)) : (¬ p18) ∨ (¬ p127) ∨ (¬ p325) ∨ (¬ p349) ∨ (¬ p477) ∨ (¬ p690) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p477 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p128 := by
    exact h653
  have u9 : (¬ p686) := by
    exact h16205
  rcases h16121 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u9 q7)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step20626 (p7 p18 p128 p210 p237 p791 p918 p959 p1226 p1273 p1452 p1490 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16213 : (¬ p791))
    (h16122 : p7 ∨ (¬ p18) ∨ (¬ p128) ∨ (¬ p210) ∨ (¬ p237) ∨ p791 ∨ (¬ p918) ∨ (¬ p959) ∨ (¬ p1226) ∨ (¬ p1273) ∨ (¬ p1452) ∨ (¬ p1490)) : (¬ p18) ∨ (¬ p210) ∨ (¬ p237) ∨ (¬ p918) ∨ (¬ p959) ∨ (¬ p1226) ∨ (¬ p1273) ∨ (¬ p1452) ∨ (¬ p1490) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p959 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1490 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p128 := by
    exact h653
  have u11 : (¬ p791) := by
    exact h16213
  rcases h16122 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u11 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step20627 (p7 p18 p127 p128 p1159 p1324 p1465 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16309 : (¬ p1324))
    (h16123 : p7 ∨ (¬ p18) ∨ (¬ p127) ∨ (¬ p128) ∨ (¬ p1159) ∨ p1324 ∨ (¬ p1465)) : (¬ p18) ∨ (¬ p127) ∨ (¬ p1159) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p128 := by
    exact h653
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h16123 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step20628 (p7 p595 p657 p734 p1135 p1136 p1542 : Prop)
    (h16152 : (¬ p7))
    (h6744 : p1135)
    (h16259 : (¬ p1136))
    (h16124 : p7 ∨ (¬ p595) ∨ (¬ p657) ∨ (¬ p734) ∨ (¬ p1135) ∨ p1136 ∨ (¬ p1542)) : (¬ p595) ∨ (¬ p657) ∨ (¬ p734) ∨ (¬ p1542) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p1135 := by
    exact h6744
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h16124 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step20629 (p7 p18 p127 p128 p657 p904 p1004 p1096 p1136 p1159 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16259 : (¬ p1136))
    (h16125 : p7 ∨ (¬ p18) ∨ (¬ p127) ∨ (¬ p128) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1004) ∨ (¬ p1096) ∨ p1136 ∨ (¬ p1159)) : (¬ p18) ∨ (¬ p127) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1004) ∨ (¬ p1096) ∨ (¬ p1159) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p128 := by
    exact h653
  have u9 : (¬ p1136) := by
    exact h16259
  rcases h16125 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u9 q8)
  · exact False.elim (q9 u6)

theorem step20631 (p2 p7 p18 p127 p128 p430 p435 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16180 : (¬ p430))
    (h16127 : (¬ p2) ∨ p7 ∨ (¬ p18) ∨ (¬ p127) ∨ (¬ p128) ∨ p430 ∨ (¬ p435)) : (¬ p2) ∨ (¬ p18) ∨ (¬ p127) ∨ (¬ p435) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p128 := by
    exact h653
  have u6 : (¬ p430) := by
    exact h16180
  rcases h16127 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step20632 (p7 p18 p63 p128 p210 p389 p789 p959 p1136 p1226 p1393 p1452 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16259 : (¬ p1136))
    (h16128 : p7 ∨ (¬ p18) ∨ (¬ p63) ∨ (¬ p128) ∨ (¬ p210) ∨ (¬ p389) ∨ (¬ p789) ∨ (¬ p959) ∨ p1136 ∨ (¬ p1226) ∨ (¬ p1393) ∨ (¬ p1452)) : (¬ p18) ∨ (¬ p63) ∨ (¬ p210) ∨ (¬ p389) ∨ (¬ p789) ∨ (¬ p959) ∨ (¬ p1226) ∨ (¬ p1393) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p959 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p128 := by
    exact h653
  have u11 : (¬ p1136) := by
    exact h16259
  rcases h16128 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u11 q8)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step20633 (p7 p8 p682 p728 p789 p1015 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16203 : (¬ p682))
    (h6744 : p1135)
    (h16129 : p7 ∨ (¬ p8) ∨ p682 ∨ (¬ p728) ∨ (¬ p789) ∨ (¬ p1015) ∨ (¬ p1135)) : (¬ p8) ∨ (¬ p728) ∨ (¬ p789) ∨ (¬ p1015) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p682) := by
    exact h16203
  have u6 : p1135 := by
    exact h6744
  rcases h16129 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step20634 (p2 p7 p18 p89 p127 p128 p224 p237 p545 p789 p839 p1136 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16259 : (¬ p1136))
    (h16130 : (¬ p2) ∨ p7 ∨ (¬ p18) ∨ (¬ p89) ∨ (¬ p127) ∨ (¬ p128) ∨ (¬ p224) ∨ (¬ p237) ∨ (¬ p545) ∨ (¬ p789) ∨ (¬ p839) ∨ p1136) : (¬ p2) ∨ (¬ p18) ∨ (¬ p89) ∨ (¬ p127) ∨ (¬ p224) ∨ (¬ p237) ∨ (¬ p545) ∨ (¬ p789) ∨ (¬ p839) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p839 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p128 := by
    exact h653
  have u11 : (¬ p1136) := by
    exact h16259
  rcases h16130 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u0)
  · exact False.elim (u9 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u8)
  · exact False.elim (u11 q11)

theorem step20635 (p2 p7 p224 p545 p1001 p1140 : Prop)
    (h16152 : (¬ p7))
    (h16131 : (¬ p2) ∨ p7 ∨ (¬ p224) ∨ (¬ p545) ∨ (¬ p1001) ∨ (¬ p1140)) : (¬ p2) ∨ (¬ p224) ∨ (¬ p545) ∨ (¬ p1001) ∨ (¬ p1140) := by
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
  have u2 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1001 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h16131 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20636 (p7 p45 p90 p101 p134 p224 p343 p686 p789 p790 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16205 : (¬ p686))
    (h16132 : p7 ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p101) ∨ (¬ p134) ∨ (¬ p224) ∨ (¬ p343) ∨ p686 ∨ (¬ p789) ∨ (¬ p790)) : (¬ p45) ∨ (¬ p90) ∨ (¬ p101) ∨ (¬ p134) ∨ (¬ p224) ∨ (¬ p789) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p343 := by
    exact h1950
  have u9 : (¬ p686) := by
    exact h16205
  rcases h16132 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u8)
  · exact False.elim (u9 q7)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step20637 (p7 p41 p42 p237 p814 p918 p1527 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16359 : (¬ p1527))
    (h16133 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p237) ∨ (¬ p814) ∨ (¬ p918) ∨ p1527) : (¬ p41) ∨ (¬ p237) ∨ (¬ p814) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p42 := by
    exact h132
  have u6 : (¬ p1527) := by
    exact h16359
  rcases h16133 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step20638 (p7 p256 p576 p814 p928 p1527 p1537 : Prop)
    (h16152 : (¬ p7))
    (h16359 : (¬ p1527))
    (h9400 : p1537)
    (h16134 : p7 ∨ (¬ p256) ∨ (¬ p576) ∨ (¬ p814) ∨ (¬ p928) ∨ p1527 ∨ (¬ p1537)) : (¬ p256) ∨ (¬ p576) ∨ (¬ p814) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p1527) := by
    exact h16359
  have u6 : p1537 := by
    exact h9400
  rcases h16134 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step20639 (p5 p6 p7 p101 p595 p669 p1076 p1286 : Prop)
    (h16152 : (¬ p7))
    (h16135 : (¬ p5) ∨ (¬ p6) ∨ p7 ∨ (¬ p101) ∨ (¬ p595) ∨ (¬ p669) ∨ (¬ p1076) ∨ (¬ p1286)) : (¬ p5) ∨ (¬ p6) ∨ (¬ p101) ∨ (¬ p595) ∨ (¬ p669) ∨ (¬ p1076) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h16135 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20640 (p5 p6 p7 p101 p132 p346 p406 p426 p581 p620 p1287 p1387 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16178 : (¬ p426))
    (h16136 : (¬ p5) ∨ (¬ p6) ∨ p7 ∨ (¬ p101) ∨ (¬ p132) ∨ (¬ p346) ∨ (¬ p406) ∨ p426 ∨ (¬ p581) ∨ (¬ p620) ∨ (¬ p1287) ∨ (¬ p1387)) : (¬ p5) ∨ (¬ p6) ∨ (¬ p101) ∨ (¬ p346) ∨ (¬ p406) ∨ (¬ p581) ∨ (¬ p620) ∨ (¬ p1287) ∨ (¬ p1387) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p620 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p132 := by
    exact h786
  have u11 : (¬ p426) := by
    exact h16178
  rcases h16136 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u9 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u11 q7)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step20641 (p5 p6 p7 p101 p346 p426 p595 p1286 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h8348 : p1386)
    (h16137 : (¬ p5) ∨ (¬ p6) ∨ p7 ∨ (¬ p101) ∨ (¬ p346) ∨ p426 ∨ (¬ p595) ∨ (¬ p1286) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p5) ∨ (¬ p6) ∨ (¬ p101) ∨ (¬ p346) ∨ (¬ p595) ∨ (¬ p1286) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p426) := by
    exact h16178
  have u9 : p1386 := by
    exact h8348
  rcases h16137 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u8 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u9)

theorem step20643 (p5 p6 p7 p41 p42 p89 p101 p346 p426 p790 p1385 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16178 : (¬ p426))
    (h16139 : (¬ p5) ∨ (¬ p6) ∨ p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p89) ∨ (¬ p101) ∨ (¬ p346) ∨ p426 ∨ (¬ p790) ∨ (¬ p1385)) : (¬ p5) ∨ (¬ p6) ∨ (¬ p41) ∨ (¬ p89) ∨ (¬ p101) ∨ (¬ p346) ∨ (¬ p790) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p42 := by
    exact h132
  have u10 : (¬ p426) := by
    exact h16178
  rcases h16139 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u8 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u10 q8)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step20644 (p5 p6 p7 p10 p63 p351 p840 p928 : Prop)
    (h16152 : (¬ p7))
    (h16140 : (¬ p5) ∨ (¬ p6) ∨ p7 ∨ (¬ p10) ∨ (¬ p63) ∨ (¬ p351) ∨ (¬ p840) ∨ (¬ p928)) : (¬ p5) ∨ (¬ p6) ∨ (¬ p10) ∨ (¬ p63) ∨ (¬ p351) ∨ (¬ p840) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h16140 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20645 (p7 p132 p581 p789 p790 p791 p1287 p1387 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16213 : (¬ p791))
    (h16141 : p7 ∨ (¬ p132) ∨ (¬ p581) ∨ (¬ p789) ∨ (¬ p790) ∨ p791 ∨ (¬ p1287) ∨ (¬ p1387)) : (¬ p581) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1287) ∨ (¬ p1387) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p132 := by
    exact h786
  have u7 : (¬ p791) := by
    exact h16213
  rcases h16141 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u7 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step20646 (p5 p6 p7 p89 p237 p918 p1206 p1273 p1490 : Prop)
    (h16152 : (¬ p7))
    (h16142 : (¬ p5) ∨ (¬ p6) ∨ p7 ∨ (¬ p89) ∨ (¬ p237) ∨ (¬ p918) ∨ (¬ p1206) ∨ (¬ p1273) ∨ (¬ p1490)) : (¬ p5) ∨ (¬ p6) ∨ (¬ p89) ∨ (¬ p237) ∨ (¬ p918) ∨ (¬ p1206) ∨ (¬ p1273) ∨ (¬ p1490) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1490 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h16142 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u8 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20647 (p5 p6 p7 p10 p224 p351 p595 p1286 : Prop)
    (h16152 : (¬ p7))
    (h16143 : (¬ p5) ∨ (¬ p6) ∨ p7 ∨ (¬ p10) ∨ (¬ p224) ∨ (¬ p351) ∨ (¬ p595) ∨ (¬ p1286)) : (¬ p5) ∨ (¬ p6) ∨ (¬ p10) ∨ (¬ p224) ∨ (¬ p351) ∨ (¬ p595) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h16143 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20648 (p7 p41 p42 p125 p224 p265 p351 p576 p789 p790 p791 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16213 : (¬ p791))
    (h16144 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p125) ∨ (¬ p224) ∨ (¬ p265) ∨ (¬ p351) ∨ (¬ p576) ∨ (¬ p789) ∨ (¬ p790) ∨ p791) : (¬ p41) ∨ (¬ p125) ∨ (¬ p224) ∨ (¬ p265) ∨ (¬ p351) ∨ (¬ p576) ∨ (¬ p789) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p42 := by
    exact h132
  have u10 : (¬ p791) := by
    exact h16213
  rcases h16144 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (u10 q10)

theorem step20649 (p5 p6 p7 p63 p389 p789 p1206 p1393 : Prop)
    (h16152 : (¬ p7))
    (h16146 : (¬ p5) ∨ (¬ p6) ∨ p7 ∨ (¬ p63) ∨ (¬ p389) ∨ (¬ p789) ∨ (¬ p1206) ∨ (¬ p1393)) : (¬ p5) ∨ (¬ p6) ∨ (¬ p63) ∨ (¬ p389) ∨ (¬ p789) ∨ (¬ p1206) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h16146 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20650 (p5 p6 p7 p8 p9 p10 p517 p657 p858 : Prop)
    (h16152 : (¬ p7))
    (h16147 : (¬ p5) ∨ (¬ p6) ∨ p7 ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p517) ∨ (¬ p657) ∨ (¬ p858)) : (¬ p5) ∨ (¬ p6) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p517) ∨ (¬ p657) ∨ (¬ p858) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p517 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h16147 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u8 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20651 (p7 p800 p858 p1002 p1035 p1325 : Prop)
    (h16152 : (¬ p7))
    (h16148 : p7 ∨ (¬ p800) ∨ (¬ p858) ∨ (¬ p1002) ∨ (¬ p1035) ∨ (¬ p1325)) : (¬ p800) ∨ (¬ p858) ∨ (¬ p1002) ∨ (¬ p1035) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p800 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1002 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h16148 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20652 (p1286 p1287 p1296 p1297 p1298 p1299 p1300 p1301 : Prop)
    (h7810 : p1296 ∨ p1301)
    (h7815 : p1297 ∨ p1301)
    (h7820 : p1298 ∨ p1301)
    (h7825 : p1299 ∨ p1301)
    (h7830 : p1300 ∨ p1301)
    (h7722 : p1286 ∨ p1287 ∨ (¬ p1296) ∨ (¬ p1297) ∨ (¬ p1298) ∨ (¬ p1299) ∨ (¬ p1300)) : p1301 ∨ p1287 ∨ p1286 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1301) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1287) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1286) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1296 := by
    rcases h7810 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1297 := by
    rcases h7815 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1298 := by
    rcases h7820 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1299 := by
    rcases h7825 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1300 := by
    rcases h7830 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7722 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20653 (p1286 p1287 p1296 p1297 p1298 p1299 p1300 p1302 : Prop)
    (h7811 : p1296 ∨ p1302)
    (h7816 : p1297 ∨ p1302)
    (h7821 : p1298 ∨ p1302)
    (h7826 : p1299 ∨ p1302)
    (h7831 : p1300 ∨ p1302)
    (h7722 : p1286 ∨ p1287 ∨ (¬ p1296) ∨ (¬ p1297) ∨ (¬ p1298) ∨ (¬ p1299) ∨ (¬ p1300)) : p1302 ∨ p1287 ∨ p1286 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1302) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1287) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1286) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1296 := by
    rcases h7811 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1297 := by
    rcases h7816 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1298 := by
    rcases h7821 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1299 := by
    rcases h7826 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1300 := by
    rcases h7831 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7722 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20654 (p1286 p1287 p1296 p1297 p1298 p1299 p1300 p1303 : Prop)
    (h7812 : p1296 ∨ p1303)
    (h7817 : p1297 ∨ p1303)
    (h7822 : p1298 ∨ p1303)
    (h7827 : p1299 ∨ p1303)
    (h7832 : p1300 ∨ p1303)
    (h7722 : p1286 ∨ p1287 ∨ (¬ p1296) ∨ (¬ p1297) ∨ (¬ p1298) ∨ (¬ p1299) ∨ (¬ p1300)) : p1303 ∨ p1287 ∨ p1286 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1287) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1286) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1296 := by
    rcases h7812 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1297 := by
    rcases h7817 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1298 := by
    rcases h7822 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1299 := by
    rcases h7827 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1300 := by
    rcases h7832 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7722 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20655 (p1286 p1287 p1296 p1297 p1298 p1299 p1300 p1304 : Prop)
    (h7813 : p1296 ∨ p1304)
    (h7818 : p1297 ∨ p1304)
    (h7823 : p1298 ∨ p1304)
    (h7828 : p1299 ∨ p1304)
    (h7833 : p1300 ∨ p1304)
    (h7722 : p1286 ∨ p1287 ∨ (¬ p1296) ∨ (¬ p1297) ∨ (¬ p1298) ∨ (¬ p1299) ∨ (¬ p1300)) : p1304 ∨ p1287 ∨ p1286 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1304) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1287) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1286) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1296 := by
    rcases h7813 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1297 := by
    rcases h7818 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1298 := by
    rcases h7823 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1299 := by
    rcases h7828 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1300 := by
    rcases h7833 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7722 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20656 (p1286 p1287 p1296 p1297 p1298 p1299 p1300 p1301 p1302 p1303 p1304 p1305 : Prop)
    (h7747 : p1286 ∨ p1287 ∨ (¬ p1301) ∨ (¬ p1302) ∨ (¬ p1303) ∨ (¬ p1304) ∨ (¬ p1305))
    (h7814 : p1296 ∨ p1305)
    (h7819 : p1297 ∨ p1305)
    (h7824 : p1298 ∨ p1305)
    (h7829 : p1299 ∨ p1305)
    (h7834 : p1300 ∨ p1305)
    (h7722 : p1286 ∨ p1287 ∨ (¬ p1296) ∨ (¬ p1297) ∨ (¬ p1298) ∨ (¬ p1299) ∨ (¬ p1300)) : (¬ p1304) ∨ (¬ p1303) ∨ p1286 ∨ p1287 ∨ (¬ p1301) ∨ (¬ p1302) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1286) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1287) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1302 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1305) := by
    rcases h7747 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1296 := by
    rcases h7814 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1297 := by
    rcases h7819 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1298 := by
    rcases h7824 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1299 := by
    rcases h7829 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1300 := by
    rcases h7834 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h7722 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20657 (p1286 p1287 p1301 p1302 p1303 p1304 : Prop)
    (h20652 : p1301 ∨ p1287 ∨ p1286)
    (h20653 : p1302 ∨ p1287 ∨ p1286)
    (h20654 : p1303 ∨ p1287 ∨ p1286)
    (h20655 : p1304 ∨ p1287 ∨ p1286)
    (h20656 : (¬ p1304) ∨ (¬ p1303) ∨ p1286 ∨ p1287 ∨ (¬ p1301) ∨ (¬ p1302)) : p1287 ∨ p1286 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1287) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1286) := fun hu => hn (Or.inr hu)
  have u2 : p1301 := by
    rcases h20652 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1302 := by
    rcases h20653 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1303 := by
    rcases h20654 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1304 := by
    rcases h20655 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20656 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20658 (p1055 p1061 p1064 p1065 p1066 p1067 p1068 p1069 : Prop)
    (h6323 : p1064 ∨ p1069)
    (h6328 : p1065 ∨ p1069)
    (h6333 : p1066 ∨ p1069)
    (h6338 : p1067 ∨ p1069)
    (h6343 : p1068 ∨ p1069)
    (h6235 : p1055 ∨ p1061 ∨ (¬ p1064) ∨ (¬ p1065) ∨ (¬ p1066) ∨ (¬ p1067) ∨ (¬ p1068)) : p1069 ∨ p1061 ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1069) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1061) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1064 := by
    rcases h6323 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1065 := by
    rcases h6328 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1066 := by
    rcases h6333 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1067 := by
    rcases h6338 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1068 := by
    rcases h6343 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6235 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20659 (p1055 p1061 p1064 p1065 p1066 p1067 p1068 p1070 : Prop)
    (h6324 : p1064 ∨ p1070)
    (h6329 : p1065 ∨ p1070)
    (h6334 : p1066 ∨ p1070)
    (h6339 : p1067 ∨ p1070)
    (h6344 : p1068 ∨ p1070)
    (h6235 : p1055 ∨ p1061 ∨ (¬ p1064) ∨ (¬ p1065) ∨ (¬ p1066) ∨ (¬ p1067) ∨ (¬ p1068)) : p1070 ∨ p1061 ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1070) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1061) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1064 := by
    rcases h6324 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1065 := by
    rcases h6329 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1066 := by
    rcases h6334 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1067 := by
    rcases h6339 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1068 := by
    rcases h6344 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6235 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20660 (p1055 p1061 p1064 p1065 p1066 p1067 p1068 p1071 : Prop)
    (h6325 : p1064 ∨ p1071)
    (h6330 : p1065 ∨ p1071)
    (h6335 : p1066 ∨ p1071)
    (h6340 : p1067 ∨ p1071)
    (h6345 : p1068 ∨ p1071)
    (h6235 : p1055 ∨ p1061 ∨ (¬ p1064) ∨ (¬ p1065) ∨ (¬ p1066) ∨ (¬ p1067) ∨ (¬ p1068)) : p1071 ∨ p1061 ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1071) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1061) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1064 := by
    rcases h6325 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1065 := by
    rcases h6330 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1066 := by
    rcases h6335 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1067 := by
    rcases h6340 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1068 := by
    rcases h6345 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6235 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20661 (p1055 p1061 p1064 p1065 p1066 p1067 p1068 p1072 : Prop)
    (h6326 : p1064 ∨ p1072)
    (h6331 : p1065 ∨ p1072)
    (h6336 : p1066 ∨ p1072)
    (h6341 : p1067 ∨ p1072)
    (h6346 : p1068 ∨ p1072)
    (h6235 : p1055 ∨ p1061 ∨ (¬ p1064) ∨ (¬ p1065) ∨ (¬ p1066) ∨ (¬ p1067) ∨ (¬ p1068)) : p1072 ∨ p1061 ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1072) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1061) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1064 := by
    rcases h6326 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1065 := by
    rcases h6331 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1066 := by
    rcases h6336 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1067 := by
    rcases h6341 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1068 := by
    rcases h6346 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6235 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20662 (p1055 p1061 p1064 p1065 p1066 p1067 p1068 p1069 p1070 p1071 p1072 p1073 : Prop)
    (h6260 : p1055 ∨ p1061 ∨ (¬ p1069) ∨ (¬ p1070) ∨ (¬ p1071) ∨ (¬ p1072) ∨ (¬ p1073))
    (h6327 : p1064 ∨ p1073)
    (h6332 : p1065 ∨ p1073)
    (h6337 : p1066 ∨ p1073)
    (h6342 : p1067 ∨ p1073)
    (h6347 : p1068 ∨ p1073)
    (h6235 : p1055 ∨ p1061 ∨ (¬ p1064) ∨ (¬ p1065) ∨ (¬ p1066) ∨ (¬ p1067) ∨ (¬ p1068)) : (¬ p1072) ∨ (¬ p1071) ∨ p1055 ∨ p1061 ∨ (¬ p1069) ∨ (¬ p1070) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1072 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1071 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1061) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1069 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1070 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1073) := by
    rcases h6260 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1064 := by
    rcases h6327 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1065 := by
    rcases h6332 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1066 := by
    rcases h6337 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1067 := by
    rcases h6342 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1068 := by
    rcases h6347 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h6235 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20663 (p1055 p1061 p1069 p1070 p1071 p1072 : Prop)
    (h20658 : p1069 ∨ p1061 ∨ p1055)
    (h20659 : p1070 ∨ p1061 ∨ p1055)
    (h20660 : p1071 ∨ p1061 ∨ p1055)
    (h20661 : p1072 ∨ p1061 ∨ p1055)
    (h20662 : (¬ p1072) ∨ (¬ p1071) ∨ p1055 ∨ p1061 ∨ (¬ p1069) ∨ (¬ p1070)) : p1061 ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1061) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr hu)
  have u2 : p1069 := by
    rcases h20658 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1070 := by
    rcases h20659 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1071 := by
    rcases h20660 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1072 := by
    rcases h20661 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20662 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20664 (p1015 p1022 p1025 p1026 p1027 p1028 p1029 p1030 : Prop)
    (h6066 : p1025 ∨ p1030)
    (h6071 : p1026 ∨ p1030)
    (h6076 : p1027 ∨ p1030)
    (h6081 : p1028 ∨ p1030)
    (h6086 : p1029 ∨ p1030)
    (h5978 : p1015 ∨ p1022 ∨ (¬ p1025) ∨ (¬ p1026) ∨ (¬ p1027) ∨ (¬ p1028) ∨ (¬ p1029)) : p1030 ∨ p1015 ∨ p1022 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1030) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1015) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1022) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1025 := by
    rcases h6066 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1026 := by
    rcases h6071 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1027 := by
    rcases h6076 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1028 := by
    rcases h6081 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1029 := by
    rcases h6086 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5978 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20665 (p1015 p1022 p1025 p1026 p1027 p1028 p1029 p1031 : Prop)
    (h6067 : p1025 ∨ p1031)
    (h6072 : p1026 ∨ p1031)
    (h6077 : p1027 ∨ p1031)
    (h6082 : p1028 ∨ p1031)
    (h6087 : p1029 ∨ p1031)
    (h5978 : p1015 ∨ p1022 ∨ (¬ p1025) ∨ (¬ p1026) ∨ (¬ p1027) ∨ (¬ p1028) ∨ (¬ p1029)) : p1031 ∨ p1015 ∨ p1022 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1031) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1015) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1022) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1025 := by
    rcases h6067 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1026 := by
    rcases h6072 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1027 := by
    rcases h6077 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1028 := by
    rcases h6082 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1029 := by
    rcases h6087 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5978 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20666 (p1015 p1022 p1025 p1026 p1027 p1028 p1029 p1032 : Prop)
    (h6068 : p1025 ∨ p1032)
    (h6073 : p1026 ∨ p1032)
    (h6078 : p1027 ∨ p1032)
    (h6083 : p1028 ∨ p1032)
    (h6088 : p1029 ∨ p1032)
    (h5978 : p1015 ∨ p1022 ∨ (¬ p1025) ∨ (¬ p1026) ∨ (¬ p1027) ∨ (¬ p1028) ∨ (¬ p1029)) : p1032 ∨ p1015 ∨ p1022 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1032) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1015) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1022) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1025 := by
    rcases h6068 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1026 := by
    rcases h6073 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1027 := by
    rcases h6078 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1028 := by
    rcases h6083 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1029 := by
    rcases h6088 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5978 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20667 (p1015 p1022 p1025 p1026 p1027 p1028 p1029 p1033 : Prop)
    (h6069 : p1025 ∨ p1033)
    (h6074 : p1026 ∨ p1033)
    (h6079 : p1027 ∨ p1033)
    (h6084 : p1028 ∨ p1033)
    (h6089 : p1029 ∨ p1033)
    (h5978 : p1015 ∨ p1022 ∨ (¬ p1025) ∨ (¬ p1026) ∨ (¬ p1027) ∨ (¬ p1028) ∨ (¬ p1029)) : p1033 ∨ p1015 ∨ p1022 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1033) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1015) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1022) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1025 := by
    rcases h6069 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1026 := by
    rcases h6074 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1027 := by
    rcases h6079 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1028 := by
    rcases h6084 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1029 := by
    rcases h6089 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5978 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20668 (p1015 p1022 p1025 p1026 p1027 p1028 p1029 p1030 p1031 p1032 p1033 p1034 : Prop)
    (h6003 : p1015 ∨ p1022 ∨ (¬ p1030) ∨ (¬ p1031) ∨ (¬ p1032) ∨ (¬ p1033) ∨ (¬ p1034))
    (h6070 : p1025 ∨ p1034)
    (h6075 : p1026 ∨ p1034)
    (h6080 : p1027 ∨ p1034)
    (h6085 : p1028 ∨ p1034)
    (h6090 : p1029 ∨ p1034)
    (h5978 : p1015 ∨ p1022 ∨ (¬ p1025) ∨ (¬ p1026) ∨ (¬ p1027) ∨ (¬ p1028) ∨ (¬ p1029)) : (¬ p1033) ∨ (¬ p1032) ∨ p1022 ∨ p1015 ∨ (¬ p1030) ∨ (¬ p1031) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1033 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1032 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1022) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1015) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1030 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1031 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1034) := by
    rcases h6003 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1025 := by
    rcases h6070 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1026 := by
    rcases h6075 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1027 := by
    rcases h6080 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1028 := by
    rcases h6085 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1029 := by
    rcases h6090 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h5978 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20669 (p1015 p1022 p1030 p1031 p1032 p1033 : Prop)
    (h20664 : p1030 ∨ p1015 ∨ p1022)
    (h20665 : p1031 ∨ p1015 ∨ p1022)
    (h20666 : p1032 ∨ p1015 ∨ p1022)
    (h20667 : p1033 ∨ p1015 ∨ p1022)
    (h20668 : (¬ p1033) ∨ (¬ p1032) ∨ p1022 ∨ p1015 ∨ (¬ p1030) ∨ (¬ p1031)) : p1015 ∨ p1022 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1015) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1022) := fun hu => hn (Or.inr hu)
  have u2 : p1030 := by
    rcases h20664 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1031 := by
    rcases h20665 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1032 := by
    rcases h20666 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1033 := by
    rcases h20667 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20668 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20670 (p1232 p1235 p1239 p1240 p1241 p1242 p1243 p1244 : Prop)
    (h7428 : p1239 ∨ p1244)
    (h7433 : p1240 ∨ p1244)
    (h7438 : p1241 ∨ p1244)
    (h7443 : p1242 ∨ p1244)
    (h7448 : p1243 ∨ p1244)
    (h7338 : p1232 ∨ p1235 ∨ (¬ p1239) ∨ (¬ p1240) ∨ (¬ p1241) ∨ (¬ p1242) ∨ (¬ p1243)) : p1244 ∨ p1235 ∨ p1232 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1244) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1235) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1232) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1239 := by
    rcases h7428 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1240 := by
    rcases h7433 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1241 := by
    rcases h7438 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1242 := by
    rcases h7443 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1243 := by
    rcases h7448 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7338 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20671 (p1232 p1235 p1239 p1240 p1241 p1242 p1243 p1245 : Prop)
    (h7429 : p1239 ∨ p1245)
    (h7434 : p1240 ∨ p1245)
    (h7439 : p1241 ∨ p1245)
    (h7444 : p1242 ∨ p1245)
    (h7449 : p1243 ∨ p1245)
    (h7338 : p1232 ∨ p1235 ∨ (¬ p1239) ∨ (¬ p1240) ∨ (¬ p1241) ∨ (¬ p1242) ∨ (¬ p1243)) : p1245 ∨ p1235 ∨ p1232 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1245) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1235) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1232) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1239 := by
    rcases h7429 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1240 := by
    rcases h7434 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1241 := by
    rcases h7439 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1242 := by
    rcases h7444 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1243 := by
    rcases h7449 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7338 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20672 (p1232 p1235 p1239 p1240 p1241 p1242 p1243 p1246 : Prop)
    (h7430 : p1239 ∨ p1246)
    (h7435 : p1240 ∨ p1246)
    (h7440 : p1241 ∨ p1246)
    (h7445 : p1242 ∨ p1246)
    (h7450 : p1243 ∨ p1246)
    (h7338 : p1232 ∨ p1235 ∨ (¬ p1239) ∨ (¬ p1240) ∨ (¬ p1241) ∨ (¬ p1242) ∨ (¬ p1243)) : p1246 ∨ p1235 ∨ p1232 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1246) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1235) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1232) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1239 := by
    rcases h7430 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1240 := by
    rcases h7435 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1241 := by
    rcases h7440 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1242 := by
    rcases h7445 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1243 := by
    rcases h7450 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7338 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20673 (p1232 p1235 p1239 p1240 p1241 p1242 p1243 p1247 : Prop)
    (h7431 : p1239 ∨ p1247)
    (h7436 : p1240 ∨ p1247)
    (h7441 : p1241 ∨ p1247)
    (h7446 : p1242 ∨ p1247)
    (h7451 : p1243 ∨ p1247)
    (h7338 : p1232 ∨ p1235 ∨ (¬ p1239) ∨ (¬ p1240) ∨ (¬ p1241) ∨ (¬ p1242) ∨ (¬ p1243)) : p1247 ∨ p1235 ∨ p1232 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1247) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1235) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1232) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1239 := by
    rcases h7431 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1240 := by
    rcases h7436 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1241 := by
    rcases h7441 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1242 := by
    rcases h7446 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1243 := by
    rcases h7451 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7338 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20674 (p1232 p1235 p1239 p1240 p1241 p1242 p1243 p1244 p1245 p1246 p1247 p1248 : Prop)
    (h7363 : p1232 ∨ p1235 ∨ (¬ p1244) ∨ (¬ p1245) ∨ (¬ p1246) ∨ (¬ p1247) ∨ (¬ p1248))
    (h7432 : p1239 ∨ p1248)
    (h7437 : p1240 ∨ p1248)
    (h7442 : p1241 ∨ p1248)
    (h7447 : p1242 ∨ p1248)
    (h7452 : p1243 ∨ p1248)
    (h7338 : p1232 ∨ p1235 ∨ (¬ p1239) ∨ (¬ p1240) ∨ (¬ p1241) ∨ (¬ p1242) ∨ (¬ p1243)) : (¬ p1247) ∨ (¬ p1246) ∨ p1232 ∨ p1235 ∨ (¬ p1244) ∨ (¬ p1245) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1247 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1246 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1232) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1235) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1244 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1245 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1248) := by
    rcases h7363 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1239 := by
    rcases h7432 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1240 := by
    rcases h7437 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1241 := by
    rcases h7442 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1242 := by
    rcases h7447 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1243 := by
    rcases h7452 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h7338 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20675 (p1232 p1235 p1244 p1245 p1246 p1247 : Prop)
    (h20670 : p1244 ∨ p1235 ∨ p1232)
    (h20671 : p1245 ∨ p1235 ∨ p1232)
    (h20672 : p1246 ∨ p1235 ∨ p1232)
    (h20673 : p1247 ∨ p1235 ∨ p1232)
    (h20674 : (¬ p1247) ∨ (¬ p1246) ∨ p1232 ∨ p1235 ∨ (¬ p1244) ∨ (¬ p1245)) : p1235 ∨ p1232 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1235) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1232) := fun hu => hn (Or.inr hu)
  have u2 : p1244 := by
    rcases h20670 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1245 := by
    rcases h20671 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1246 := by
    rcases h20672 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1247 := by
    rcases h20673 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20674 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20676 (p997 p1001 p1005 p1006 p1007 p1008 p1009 p1010 : Prop)
    (h5938 : p1005 ∨ p1010)
    (h5943 : p1006 ∨ p1010)
    (h5948 : p1007 ∨ p1010)
    (h5953 : p1008 ∨ p1010)
    (h5958 : p1009 ∨ p1010)
    (h5838 : p997 ∨ p1001 ∨ (¬ p1005) ∨ (¬ p1006) ∨ (¬ p1007) ∨ (¬ p1008) ∨ (¬ p1009)) : p1010 ∨ p997 ∨ p1001 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1010) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p997) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1001) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1005 := by
    rcases h5938 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1006 := by
    rcases h5943 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1007 := by
    rcases h5948 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1008 := by
    rcases h5953 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1009 := by
    rcases h5958 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5838 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20677 (p997 p1001 p1005 p1006 p1007 p1008 p1009 p1011 : Prop)
    (h5939 : p1005 ∨ p1011)
    (h5944 : p1006 ∨ p1011)
    (h5949 : p1007 ∨ p1011)
    (h5954 : p1008 ∨ p1011)
    (h5959 : p1009 ∨ p1011)
    (h5838 : p997 ∨ p1001 ∨ (¬ p1005) ∨ (¬ p1006) ∨ (¬ p1007) ∨ (¬ p1008) ∨ (¬ p1009)) : p1011 ∨ p997 ∨ p1001 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1011) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p997) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1001) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1005 := by
    rcases h5939 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1006 := by
    rcases h5944 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1007 := by
    rcases h5949 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1008 := by
    rcases h5954 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1009 := by
    rcases h5959 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5838 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20678 (p997 p1001 p1005 p1006 p1007 p1008 p1009 p1012 : Prop)
    (h5940 : p1005 ∨ p1012)
    (h5945 : p1006 ∨ p1012)
    (h5950 : p1007 ∨ p1012)
    (h5955 : p1008 ∨ p1012)
    (h5960 : p1009 ∨ p1012)
    (h5838 : p997 ∨ p1001 ∨ (¬ p1005) ∨ (¬ p1006) ∨ (¬ p1007) ∨ (¬ p1008) ∨ (¬ p1009)) : p1012 ∨ p997 ∨ p1001 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1012) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p997) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1001) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1005 := by
    rcases h5940 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1006 := by
    rcases h5945 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1007 := by
    rcases h5950 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1008 := by
    rcases h5955 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1009 := by
    rcases h5960 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5838 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20679 (p997 p1001 p1005 p1006 p1007 p1008 p1009 p1013 : Prop)
    (h5941 : p1005 ∨ p1013)
    (h5946 : p1006 ∨ p1013)
    (h5951 : p1007 ∨ p1013)
    (h5956 : p1008 ∨ p1013)
    (h5961 : p1009 ∨ p1013)
    (h5838 : p997 ∨ p1001 ∨ (¬ p1005) ∨ (¬ p1006) ∨ (¬ p1007) ∨ (¬ p1008) ∨ (¬ p1009)) : p1013 ∨ p997 ∨ p1001 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1013) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p997) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1001) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1005 := by
    rcases h5941 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1006 := by
    rcases h5946 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1007 := by
    rcases h5951 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1008 := by
    rcases h5956 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1009 := by
    rcases h5961 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5838 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20680 (p997 p1001 p1005 p1006 p1007 p1008 p1009 p1010 p1011 p1012 p1013 p1014 : Prop)
    (h5863 : p997 ∨ p1001 ∨ (¬ p1010) ∨ (¬ p1011) ∨ (¬ p1012) ∨ (¬ p1013) ∨ (¬ p1014))
    (h5942 : p1005 ∨ p1014)
    (h5947 : p1006 ∨ p1014)
    (h5952 : p1007 ∨ p1014)
    (h5957 : p1008 ∨ p1014)
    (h5962 : p1009 ∨ p1014)
    (h5838 : p997 ∨ p1001 ∨ (¬ p1005) ∨ (¬ p1006) ∨ (¬ p1007) ∨ (¬ p1008) ∨ (¬ p1009)) : (¬ p1013) ∨ (¬ p1012) ∨ p1001 ∨ p997 ∨ (¬ p1010) ∨ (¬ p1011) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1013 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1012 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1001) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p997) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1010 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1011 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1014) := by
    rcases h5863 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1005 := by
    rcases h5942 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1006 := by
    rcases h5947 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1007 := by
    rcases h5952 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1008 := by
    rcases h5957 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1009 := by
    rcases h5962 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h5838 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20681 (p997 p1001 p1010 p1011 p1012 p1013 : Prop)
    (h20676 : p1010 ∨ p997 ∨ p1001)
    (h20677 : p1011 ∨ p997 ∨ p1001)
    (h20678 : p1012 ∨ p997 ∨ p1001)
    (h20679 : p1013 ∨ p997 ∨ p1001)
    (h20680 : (¬ p1013) ∨ (¬ p1012) ∨ p1001 ∨ p997 ∨ (¬ p1010) ∨ (¬ p1011)) : p997 ∨ p1001 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p997) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1001) := fun hu => hn (Or.inr hu)
  have u2 : p1010 := by
    rcases h20676 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1011 := by
    rcases h20677 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1012 := by
    rcases h20678 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1013 := by
    rcases h20679 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20680 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20682 (p980 p983 p986 p987 p988 p989 p990 p991 : Prop)
    (h5812 : p986 ∨ p991)
    (h5817 : p987 ∨ p991)
    (h5822 : p988 ∨ p991)
    (h5827 : p989 ∨ p991)
    (h5832 : p990 ∨ p991)
    (h5724 : p980 ∨ p983 ∨ (¬ p986) ∨ (¬ p987) ∨ (¬ p988) ∨ (¬ p989) ∨ (¬ p990)) : p991 ∨ p980 ∨ p983 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p991) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p983) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p986 := by
    rcases h5812 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p987 := by
    rcases h5817 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p988 := by
    rcases h5822 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p989 := by
    rcases h5827 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p990 := by
    rcases h5832 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5724 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20683 (p980 p983 p986 p987 p988 p989 p990 p992 : Prop)
    (h5813 : p986 ∨ p992)
    (h5818 : p987 ∨ p992)
    (h5823 : p988 ∨ p992)
    (h5828 : p989 ∨ p992)
    (h5833 : p990 ∨ p992)
    (h5724 : p980 ∨ p983 ∨ (¬ p986) ∨ (¬ p987) ∨ (¬ p988) ∨ (¬ p989) ∨ (¬ p990)) : p992 ∨ p980 ∨ p983 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p992) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p983) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p986 := by
    rcases h5813 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p987 := by
    rcases h5818 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p988 := by
    rcases h5823 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p989 := by
    rcases h5828 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p990 := by
    rcases h5833 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5724 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20684 (p980 p983 p986 p987 p988 p989 p990 p993 : Prop)
    (h5814 : p986 ∨ p993)
    (h5819 : p987 ∨ p993)
    (h5824 : p988 ∨ p993)
    (h5829 : p989 ∨ p993)
    (h5834 : p990 ∨ p993)
    (h5724 : p980 ∨ p983 ∨ (¬ p986) ∨ (¬ p987) ∨ (¬ p988) ∨ (¬ p989) ∨ (¬ p990)) : p993 ∨ p980 ∨ p983 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p993) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p983) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p986 := by
    rcases h5814 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p987 := by
    rcases h5819 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p988 := by
    rcases h5824 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p989 := by
    rcases h5829 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p990 := by
    rcases h5834 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5724 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20685 (p980 p983 p986 p987 p988 p989 p990 p994 : Prop)
    (h5815 : p986 ∨ p994)
    (h5820 : p987 ∨ p994)
    (h5825 : p988 ∨ p994)
    (h5830 : p989 ∨ p994)
    (h5835 : p990 ∨ p994)
    (h5724 : p980 ∨ p983 ∨ (¬ p986) ∨ (¬ p987) ∨ (¬ p988) ∨ (¬ p989) ∨ (¬ p990)) : p994 ∨ p980 ∨ p983 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p994) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p983) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p986 := by
    rcases h5815 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p987 := by
    rcases h5820 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p988 := by
    rcases h5825 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p989 := by
    rcases h5830 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p990 := by
    rcases h5835 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5724 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20686 (p980 p983 p986 p987 p988 p989 p990 p991 p992 p993 p994 p995 : Prop)
    (h5749 : p980 ∨ p983 ∨ (¬ p991) ∨ (¬ p992) ∨ (¬ p993) ∨ (¬ p994) ∨ (¬ p995))
    (h5816 : p986 ∨ p995)
    (h5821 : p987 ∨ p995)
    (h5826 : p988 ∨ p995)
    (h5831 : p989 ∨ p995)
    (h5836 : p990 ∨ p995)
    (h5724 : p980 ∨ p983 ∨ (¬ p986) ∨ (¬ p987) ∨ (¬ p988) ∨ (¬ p989) ∨ (¬ p990)) : (¬ p994) ∨ (¬ p993) ∨ p983 ∨ p980 ∨ (¬ p991) ∨ (¬ p992) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p994 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p993 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p983) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p991 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p992 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p995) := by
    rcases h5749 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p986 := by
    rcases h5816 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p987 := by
    rcases h5821 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p988 := by
    rcases h5826 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p989 := by
    rcases h5831 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p990 := by
    rcases h5836 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h5724 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20687 (p980 p983 p991 p992 p993 p994 : Prop)
    (h20682 : p991 ∨ p980 ∨ p983)
    (h20683 : p992 ∨ p980 ∨ p983)
    (h20684 : p993 ∨ p980 ∨ p983)
    (h20685 : p994 ∨ p980 ∨ p983)
    (h20686 : (¬ p994) ∨ (¬ p993) ∨ p983 ∨ p980 ∨ (¬ p991) ∨ (¬ p992)) : p980 ∨ p983 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p983) := fun hu => hn (Or.inr hu)
  have u2 : p991 := by
    rcases h20682 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p992 := by
    rcases h20683 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p993 := by
    rcases h20684 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p994 := by
    rcases h20685 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20686 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20688 (p227 p959 p967 p968 p969 p970 p971 p972 : Prop)
    (h5686 : p967 ∨ p972)
    (h5691 : p968 ∨ p972)
    (h5696 : p969 ∨ p972)
    (h5701 : p970 ∨ p972)
    (h5706 : p971 ∨ p972)
    (h5588 : p227 ∨ p959 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : p972 ∨ p227 ∨ p959 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p972) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p227) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p959) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p967 := by
    rcases h5686 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p968 := by
    rcases h5691 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p969 := by
    rcases h5696 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p970 := by
    rcases h5701 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p971 := by
    rcases h5706 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5588 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20689 (p227 p959 p967 p968 p969 p970 p971 p973 : Prop)
    (h5687 : p967 ∨ p973)
    (h5692 : p968 ∨ p973)
    (h5697 : p969 ∨ p973)
    (h5702 : p970 ∨ p973)
    (h5707 : p971 ∨ p973)
    (h5588 : p227 ∨ p959 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : p973 ∨ p227 ∨ p959 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p973) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p227) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p959) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p967 := by
    rcases h5687 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p968 := by
    rcases h5692 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p969 := by
    rcases h5697 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p970 := by
    rcases h5702 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p971 := by
    rcases h5707 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5588 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20690 (p227 p959 p967 p968 p969 p970 p971 p974 : Prop)
    (h5688 : p967 ∨ p974)
    (h5693 : p968 ∨ p974)
    (h5698 : p969 ∨ p974)
    (h5703 : p970 ∨ p974)
    (h5708 : p971 ∨ p974)
    (h5588 : p227 ∨ p959 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : p974 ∨ p227 ∨ p959 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p974) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p227) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p959) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p967 := by
    rcases h5688 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p968 := by
    rcases h5693 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p969 := by
    rcases h5698 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p970 := by
    rcases h5703 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p971 := by
    rcases h5708 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5588 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20691 (p227 p959 p967 p968 p969 p970 p971 p975 : Prop)
    (h5689 : p967 ∨ p975)
    (h5694 : p968 ∨ p975)
    (h5699 : p969 ∨ p975)
    (h5704 : p970 ∨ p975)
    (h5709 : p971 ∨ p975)
    (h5588 : p227 ∨ p959 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : p975 ∨ p227 ∨ p959 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p975) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p227) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p959) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p967 := by
    rcases h5689 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p968 := by
    rcases h5694 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p969 := by
    rcases h5699 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p970 := by
    rcases h5704 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p971 := by
    rcases h5709 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5588 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20692 (p227 p959 p967 p968 p969 p970 p971 p972 p973 p974 p975 p976 : Prop)
    (h5613 : p227 ∨ p959 ∨ (¬ p972) ∨ (¬ p973) ∨ (¬ p974) ∨ (¬ p975) ∨ (¬ p976))
    (h5690 : p967 ∨ p976)
    (h5695 : p968 ∨ p976)
    (h5700 : p969 ∨ p976)
    (h5705 : p970 ∨ p976)
    (h5710 : p971 ∨ p976)
    (h5588 : p227 ∨ p959 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : (¬ p975) ∨ (¬ p974) ∨ p959 ∨ p227 ∨ (¬ p972) ∨ (¬ p973) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p975 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p974 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p959) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p227) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p972 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p973 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p976) := by
    rcases h5613 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p967 := by
    rcases h5690 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p968 := by
    rcases h5695 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p969 := by
    rcases h5700 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p970 := by
    rcases h5705 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p971 := by
    rcases h5710 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h5588 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20693 (p227 p959 p972 p973 p974 p975 : Prop)
    (h20688 : p972 ∨ p227 ∨ p959)
    (h20689 : p973 ∨ p227 ∨ p959)
    (h20690 : p974 ∨ p227 ∨ p959)
    (h20691 : p975 ∨ p227 ∨ p959)
    (h20692 : (¬ p975) ∨ (¬ p974) ∨ p959 ∨ p227 ∨ (¬ p972) ∨ (¬ p973)) : p227 ∨ p959 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p227) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p959) := fun hu => hn (Or.inr hu)
  have u2 : p972 := by
    rcases h20688 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p973 := by
    rcases h20689 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p974 := by
    rcases h20690 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p975 := by
    rcases h20691 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20692 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20694 (p1079 p1083 p1085 p1086 p1087 p1088 p1089 p1090 : Prop)
    (h6450 : p1085 ∨ p1090)
    (h6455 : p1086 ∨ p1090)
    (h6460 : p1087 ∨ p1090)
    (h6465 : p1088 ∨ p1090)
    (h6470 : p1089 ∨ p1090)
    (h6356 : p1079 ∨ p1083 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089)) : p1090 ∨ p1079 ∨ p1083 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1090) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1079) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1083) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1085 := by
    rcases h6450 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1086 := by
    rcases h6455 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1087 := by
    rcases h6460 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1088 := by
    rcases h6465 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1089 := by
    rcases h6470 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6356 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20695 (p1079 p1083 p1085 p1086 p1087 p1088 p1089 p1091 : Prop)
    (h6451 : p1085 ∨ p1091)
    (h6456 : p1086 ∨ p1091)
    (h6461 : p1087 ∨ p1091)
    (h6466 : p1088 ∨ p1091)
    (h6471 : p1089 ∨ p1091)
    (h6356 : p1079 ∨ p1083 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089)) : p1091 ∨ p1079 ∨ p1083 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1091) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1079) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1083) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1085 := by
    rcases h6451 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1086 := by
    rcases h6456 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1087 := by
    rcases h6461 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1088 := by
    rcases h6466 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1089 := by
    rcases h6471 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6356 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20696 (p1079 p1083 p1085 p1086 p1087 p1088 p1089 p1092 : Prop)
    (h6452 : p1085 ∨ p1092)
    (h6457 : p1086 ∨ p1092)
    (h6462 : p1087 ∨ p1092)
    (h6467 : p1088 ∨ p1092)
    (h6472 : p1089 ∨ p1092)
    (h6356 : p1079 ∨ p1083 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089)) : p1092 ∨ p1079 ∨ p1083 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1092) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1079) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1083) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1085 := by
    rcases h6452 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1086 := by
    rcases h6457 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1087 := by
    rcases h6462 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1088 := by
    rcases h6467 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1089 := by
    rcases h6472 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6356 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20697 (p1079 p1083 p1085 p1086 p1087 p1088 p1089 p1093 : Prop)
    (h6453 : p1085 ∨ p1093)
    (h6458 : p1086 ∨ p1093)
    (h6463 : p1087 ∨ p1093)
    (h6468 : p1088 ∨ p1093)
    (h6473 : p1089 ∨ p1093)
    (h6356 : p1079 ∨ p1083 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089)) : p1093 ∨ p1079 ∨ p1083 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1093) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1079) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1083) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1085 := by
    rcases h6453 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1086 := by
    rcases h6458 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1087 := by
    rcases h6463 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1088 := by
    rcases h6468 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1089 := by
    rcases h6473 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6356 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20698 (p1079 p1083 p1085 p1086 p1087 p1088 p1089 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h6381 : p1079 ∨ p1083 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094))
    (h6454 : p1085 ∨ p1094)
    (h6459 : p1086 ∨ p1094)
    (h6464 : p1087 ∨ p1094)
    (h6469 : p1088 ∨ p1094)
    (h6474 : p1089 ∨ p1094)
    (h6356 : p1079 ∨ p1083 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089)) : (¬ p1093) ∨ (¬ p1092) ∨ p1079 ∨ p1083 ∨ (¬ p1090) ∨ (¬ p1091) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1093 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1092 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1079) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1083) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1090 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1091 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1094) := by
    rcases h6381 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1085 := by
    rcases h6454 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1086 := by
    rcases h6459 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1087 := by
    rcases h6464 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1088 := by
    rcases h6469 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1089 := by
    rcases h6474 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h6356 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20699 (p1079 p1083 p1090 p1091 p1092 p1093 : Prop)
    (h20694 : p1090 ∨ p1079 ∨ p1083)
    (h20695 : p1091 ∨ p1079 ∨ p1083)
    (h20696 : p1092 ∨ p1079 ∨ p1083)
    (h20697 : p1093 ∨ p1079 ∨ p1083)
    (h20698 : (¬ p1093) ∨ (¬ p1092) ∨ p1079 ∨ p1083 ∨ (¬ p1090) ∨ (¬ p1091)) : p1079 ∨ p1083 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1079) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1083) := fun hu => hn (Or.inr hu)
  have u2 : p1090 := by
    rcases h20694 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1091 := by
    rcases h20695 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1092 := by
    rcases h20696 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1093 := by
    rcases h20697 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20698 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20706 (p14 p880 p887 p888 p889 p890 p891 p892 : Prop)
    (h5175 : p887 ∨ p892)
    (h5180 : p888 ∨ p892)
    (h5185 : p889 ∨ p892)
    (h5190 : p890 ∨ p892)
    (h5195 : p891 ∨ p892)
    (h5082 : p14 ∨ p880 ∨ (¬ p887) ∨ (¬ p888) ∨ (¬ p889) ∨ (¬ p890) ∨ (¬ p891)) : p892 ∨ p880 ∨ p14 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p892) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p880) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p14) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p887 := by
    rcases h5175 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p888 := by
    rcases h5180 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p889 := by
    rcases h5185 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p890 := by
    rcases h5190 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p891 := by
    rcases h5195 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5082 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20707 (p14 p880 p887 p888 p889 p890 p891 p893 : Prop)
    (h5176 : p887 ∨ p893)
    (h5181 : p888 ∨ p893)
    (h5186 : p889 ∨ p893)
    (h5191 : p890 ∨ p893)
    (h5196 : p891 ∨ p893)
    (h5082 : p14 ∨ p880 ∨ (¬ p887) ∨ (¬ p888) ∨ (¬ p889) ∨ (¬ p890) ∨ (¬ p891)) : p893 ∨ p880 ∨ p14 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p893) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p880) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p14) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p887 := by
    rcases h5176 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p888 := by
    rcases h5181 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p889 := by
    rcases h5186 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p890 := by
    rcases h5191 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p891 := by
    rcases h5196 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5082 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20708 (p14 p880 p887 p888 p889 p890 p891 p894 : Prop)
    (h5177 : p887 ∨ p894)
    (h5182 : p888 ∨ p894)
    (h5187 : p889 ∨ p894)
    (h5192 : p890 ∨ p894)
    (h5197 : p891 ∨ p894)
    (h5082 : p14 ∨ p880 ∨ (¬ p887) ∨ (¬ p888) ∨ (¬ p889) ∨ (¬ p890) ∨ (¬ p891)) : p894 ∨ p880 ∨ p14 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p894) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p880) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p14) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p887 := by
    rcases h5177 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p888 := by
    rcases h5182 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p889 := by
    rcases h5187 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p890 := by
    rcases h5192 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p891 := by
    rcases h5197 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5082 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20709 (p14 p880 p887 p888 p889 p890 p891 p895 : Prop)
    (h5178 : p887 ∨ p895)
    (h5183 : p888 ∨ p895)
    (h5188 : p889 ∨ p895)
    (h5193 : p890 ∨ p895)
    (h5198 : p891 ∨ p895)
    (h5082 : p14 ∨ p880 ∨ (¬ p887) ∨ (¬ p888) ∨ (¬ p889) ∨ (¬ p890) ∨ (¬ p891)) : p895 ∨ p880 ∨ p14 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p895) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p880) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p14) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p887 := by
    rcases h5178 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p888 := by
    rcases h5183 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p889 := by
    rcases h5188 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p890 := by
    rcases h5193 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p891 := by
    rcases h5198 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5082 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20710 (p14 p880 p887 p888 p889 p890 p891 p892 p893 p894 p895 p896 : Prop)
    (h5107 : p14 ∨ p880 ∨ (¬ p892) ∨ (¬ p893) ∨ (¬ p894) ∨ (¬ p895) ∨ (¬ p896))
    (h5179 : p887 ∨ p896)
    (h5184 : p888 ∨ p896)
    (h5189 : p889 ∨ p896)
    (h5194 : p890 ∨ p896)
    (h5199 : p891 ∨ p896)
    (h5082 : p14 ∨ p880 ∨ (¬ p887) ∨ (¬ p888) ∨ (¬ p889) ∨ (¬ p890) ∨ (¬ p891)) : (¬ p895) ∨ (¬ p894) ∨ p14 ∨ p880 ∨ (¬ p892) ∨ (¬ p893) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p895 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p894 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p880) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p892 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p893 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p896) := by
    rcases h5107 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p887 := by
    rcases h5179 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p888 := by
    rcases h5184 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p889 := by
    rcases h5189 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p890 := by
    rcases h5194 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p891 := by
    rcases h5199 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h5082 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20711 (p14 p880 p892 p893 p894 p895 : Prop)
    (h20706 : p892 ∨ p880 ∨ p14)
    (h20707 : p893 ∨ p880 ∨ p14)
    (h20708 : p894 ∨ p880 ∨ p14)
    (h20709 : p895 ∨ p880 ∨ p14)
    (h20710 : (¬ p895) ∨ (¬ p894) ∨ p14 ∨ p880 ∨ (¬ p892) ∨ (¬ p893)) : p880 ∨ p14 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p880) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p14) := fun hu => hn (Or.inr hu)
  have u2 : p892 := by
    rcases h20706 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p893 := by
    rcases h20707 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p894 := by
    rcases h20708 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p895 := by
    rcases h20709 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20710 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20712 (p1036 p1041 p1045 p1046 p1047 p1048 p1049 p1050 : Prop)
    (h6196 : p1045 ∨ p1050)
    (h6201 : p1046 ∨ p1050)
    (h6206 : p1047 ∨ p1050)
    (h6211 : p1048 ∨ p1050)
    (h6216 : p1049 ∨ p1050)
    (h6106 : p1036 ∨ p1041 ∨ (¬ p1045) ∨ (¬ p1046) ∨ (¬ p1047) ∨ (¬ p1048) ∨ (¬ p1049)) : p1050 ∨ p1036 ∨ p1041 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1050) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1036) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1041) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1045 := by
    rcases h6196 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1046 := by
    rcases h6201 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1047 := by
    rcases h6206 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1048 := by
    rcases h6211 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1049 := by
    rcases h6216 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6106 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20713 (p1036 p1041 p1045 p1046 p1047 p1048 p1049 p1051 : Prop)
    (h6197 : p1045 ∨ p1051)
    (h6202 : p1046 ∨ p1051)
    (h6207 : p1047 ∨ p1051)
    (h6212 : p1048 ∨ p1051)
    (h6217 : p1049 ∨ p1051)
    (h6106 : p1036 ∨ p1041 ∨ (¬ p1045) ∨ (¬ p1046) ∨ (¬ p1047) ∨ (¬ p1048) ∨ (¬ p1049)) : p1051 ∨ p1036 ∨ p1041 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1051) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1036) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1041) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1045 := by
    rcases h6197 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1046 := by
    rcases h6202 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1047 := by
    rcases h6207 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1048 := by
    rcases h6212 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1049 := by
    rcases h6217 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6106 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20714 (p1036 p1041 p1045 p1046 p1047 p1048 p1049 p1052 : Prop)
    (h6198 : p1045 ∨ p1052)
    (h6203 : p1046 ∨ p1052)
    (h6208 : p1047 ∨ p1052)
    (h6213 : p1048 ∨ p1052)
    (h6218 : p1049 ∨ p1052)
    (h6106 : p1036 ∨ p1041 ∨ (¬ p1045) ∨ (¬ p1046) ∨ (¬ p1047) ∨ (¬ p1048) ∨ (¬ p1049)) : p1052 ∨ p1036 ∨ p1041 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1052) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1036) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1041) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1045 := by
    rcases h6198 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1046 := by
    rcases h6203 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1047 := by
    rcases h6208 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1048 := by
    rcases h6213 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1049 := by
    rcases h6218 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6106 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20715 (p1036 p1041 p1045 p1046 p1047 p1048 p1049 p1053 : Prop)
    (h6199 : p1045 ∨ p1053)
    (h6204 : p1046 ∨ p1053)
    (h6209 : p1047 ∨ p1053)
    (h6214 : p1048 ∨ p1053)
    (h6219 : p1049 ∨ p1053)
    (h6106 : p1036 ∨ p1041 ∨ (¬ p1045) ∨ (¬ p1046) ∨ (¬ p1047) ∨ (¬ p1048) ∨ (¬ p1049)) : p1053 ∨ p1036 ∨ p1041 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1053) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1036) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1041) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1045 := by
    rcases h6199 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1046 := by
    rcases h6204 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1047 := by
    rcases h6209 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1048 := by
    rcases h6214 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1049 := by
    rcases h6219 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6106 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20716 (p1036 p1041 p1045 p1046 p1047 p1048 p1049 p1050 p1051 p1052 p1053 p1054 : Prop)
    (h6131 : p1036 ∨ p1041 ∨ (¬ p1050) ∨ (¬ p1051) ∨ (¬ p1052) ∨ (¬ p1053) ∨ (¬ p1054))
    (h6200 : p1045 ∨ p1054)
    (h6205 : p1046 ∨ p1054)
    (h6210 : p1047 ∨ p1054)
    (h6215 : p1048 ∨ p1054)
    (h6220 : p1049 ∨ p1054)
    (h6106 : p1036 ∨ p1041 ∨ (¬ p1045) ∨ (¬ p1046) ∨ (¬ p1047) ∨ (¬ p1048) ∨ (¬ p1049)) : (¬ p1053) ∨ (¬ p1052) ∨ p1041 ∨ p1036 ∨ (¬ p1050) ∨ (¬ p1051) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1053 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1052 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1041) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1036) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1050 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1051 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1054) := by
    rcases h6131 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1045 := by
    rcases h6200 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1046 := by
    rcases h6205 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1047 := by
    rcases h6210 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1048 := by
    rcases h6215 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1049 := by
    rcases h6220 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h6106 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20717 (p1036 p1041 p1050 p1051 p1052 p1053 : Prop)
    (h20712 : p1050 ∨ p1036 ∨ p1041)
    (h20713 : p1051 ∨ p1036 ∨ p1041)
    (h20714 : p1052 ∨ p1036 ∨ p1041)
    (h20715 : p1053 ∨ p1036 ∨ p1041)
    (h20716 : (¬ p1053) ∨ (¬ p1052) ∨ p1041 ∨ p1036 ∨ (¬ p1050) ∨ (¬ p1051)) : p1036 ∨ p1041 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1036) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1041) := fun hu => hn (Or.inr hu)
  have u2 : p1050 := by
    rcases h20712 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1051 := by
    rcases h20713 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1052 := by
    rcases h20714 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1053 := by
    rcases h20715 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20716 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20718 (p423 p1141 p1149 p1150 p1151 p1152 p1153 p1154 : Prop)
    (h6864 : p1149 ∨ p1154)
    (h6869 : p1150 ∨ p1154)
    (h6874 : p1151 ∨ p1154)
    (h6879 : p1152 ∨ p1154)
    (h6884 : p1153 ∨ p1154)
    (h6776 : p423 ∨ p1141 ∨ (¬ p1149) ∨ (¬ p1150) ∨ (¬ p1151) ∨ (¬ p1152) ∨ (¬ p1153)) : p1154 ∨ p423 ∨ p1141 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1154) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p423) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1141) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1149 := by
    rcases h6864 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1150 := by
    rcases h6869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1151 := by
    rcases h6874 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1152 := by
    rcases h6879 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1153 := by
    rcases h6884 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6776 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20719 (p423 p1141 p1149 p1150 p1151 p1152 p1153 p1155 : Prop)
    (h6865 : p1149 ∨ p1155)
    (h6870 : p1150 ∨ p1155)
    (h6875 : p1151 ∨ p1155)
    (h6880 : p1152 ∨ p1155)
    (h6885 : p1153 ∨ p1155)
    (h6776 : p423 ∨ p1141 ∨ (¬ p1149) ∨ (¬ p1150) ∨ (¬ p1151) ∨ (¬ p1152) ∨ (¬ p1153)) : p1155 ∨ p423 ∨ p1141 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1155) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p423) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1141) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1149 := by
    rcases h6865 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1150 := by
    rcases h6870 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1151 := by
    rcases h6875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1152 := by
    rcases h6880 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1153 := by
    rcases h6885 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6776 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20720 (p423 p1141 p1149 p1150 p1151 p1152 p1153 p1156 : Prop)
    (h6866 : p1149 ∨ p1156)
    (h6871 : p1150 ∨ p1156)
    (h6876 : p1151 ∨ p1156)
    (h6881 : p1152 ∨ p1156)
    (h6886 : p1153 ∨ p1156)
    (h6776 : p423 ∨ p1141 ∨ (¬ p1149) ∨ (¬ p1150) ∨ (¬ p1151) ∨ (¬ p1152) ∨ (¬ p1153)) : p1156 ∨ p423 ∨ p1141 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1156) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p423) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1141) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1149 := by
    rcases h6866 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1150 := by
    rcases h6871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1151 := by
    rcases h6876 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1152 := by
    rcases h6881 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1153 := by
    rcases h6886 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6776 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20721 (p423 p1141 p1149 p1150 p1151 p1152 p1153 p1157 : Prop)
    (h6867 : p1149 ∨ p1157)
    (h6872 : p1150 ∨ p1157)
    (h6877 : p1151 ∨ p1157)
    (h6882 : p1152 ∨ p1157)
    (h6887 : p1153 ∨ p1157)
    (h6776 : p423 ∨ p1141 ∨ (¬ p1149) ∨ (¬ p1150) ∨ (¬ p1151) ∨ (¬ p1152) ∨ (¬ p1153)) : p1157 ∨ p423 ∨ p1141 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1157) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p423) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1141) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1149 := by
    rcases h6867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1150 := by
    rcases h6872 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1151 := by
    rcases h6877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1152 := by
    rcases h6882 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1153 := by
    rcases h6887 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6776 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20722 (p423 p1141 p1149 p1150 p1151 p1152 p1153 p1154 p1155 p1156 p1157 p1158 : Prop)
    (h6801 : p423 ∨ p1141 ∨ (¬ p1154) ∨ (¬ p1155) ∨ (¬ p1156) ∨ (¬ p1157) ∨ (¬ p1158))
    (h6868 : p1149 ∨ p1158)
    (h6873 : p1150 ∨ p1158)
    (h6878 : p1151 ∨ p1158)
    (h6883 : p1152 ∨ p1158)
    (h6888 : p1153 ∨ p1158)
    (h6776 : p423 ∨ p1141 ∨ (¬ p1149) ∨ (¬ p1150) ∨ (¬ p1151) ∨ (¬ p1152) ∨ (¬ p1153)) : (¬ p1157) ∨ (¬ p1156) ∨ p1141 ∨ p423 ∨ (¬ p1154) ∨ (¬ p1155) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1157 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1141) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p423) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1154 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1155 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1158) := by
    rcases h6801 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1149 := by
    rcases h6868 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1150 := by
    rcases h6873 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1151 := by
    rcases h6878 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1152 := by
    rcases h6883 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1153 := by
    rcases h6888 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h6776 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20723 (p423 p1141 p1154 p1155 p1156 p1157 : Prop)
    (h20718 : p1154 ∨ p423 ∨ p1141)
    (h20719 : p1155 ∨ p423 ∨ p1141)
    (h20720 : p1156 ∨ p423 ∨ p1141)
    (h20721 : p1157 ∨ p423 ∨ p1141)
    (h20722 : (¬ p1157) ∨ (¬ p1156) ∨ p1141 ∨ p423 ∨ (¬ p1154) ∨ (¬ p1155)) : p423 ∨ p1141 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1141) := fun hu => hn (Or.inr hu)
  have u2 : p1154 := by
    rcases h20718 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1155 := by
    rcases h20719 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1156 := by
    rcases h20720 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1157 := by
    rcases h20721 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20722 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20724 (p796 p801 p804 p805 p806 p807 p808 p809 : Prop)
    (h4643 : p804 ∨ p809)
    (h4648 : p805 ∨ p809)
    (h4653 : p806 ∨ p809)
    (h4658 : p807 ∨ p809)
    (h4663 : p808 ∨ p809)
    (h4553 : p796 ∨ p801 ∨ (¬ p804) ∨ (¬ p805) ∨ (¬ p806) ∨ (¬ p807) ∨ (¬ p808)) : p809 ∨ p796 ∨ p801 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p809) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p796) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p801) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p804 := by
    rcases h4643 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p805 := by
    rcases h4648 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p806 := by
    rcases h4653 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p807 := by
    rcases h4658 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p808 := by
    rcases h4663 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4553 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20725 (p796 p801 p804 p805 p806 p807 p808 p810 : Prop)
    (h4644 : p804 ∨ p810)
    (h4649 : p805 ∨ p810)
    (h4654 : p806 ∨ p810)
    (h4659 : p807 ∨ p810)
    (h4664 : p808 ∨ p810)
    (h4553 : p796 ∨ p801 ∨ (¬ p804) ∨ (¬ p805) ∨ (¬ p806) ∨ (¬ p807) ∨ (¬ p808)) : p810 ∨ p796 ∨ p801 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p810) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p796) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p801) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p804 := by
    rcases h4644 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p805 := by
    rcases h4649 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p806 := by
    rcases h4654 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p807 := by
    rcases h4659 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p808 := by
    rcases h4664 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4553 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20726 (p796 p801 p804 p805 p806 p807 p808 p811 : Prop)
    (h4645 : p804 ∨ p811)
    (h4650 : p805 ∨ p811)
    (h4655 : p806 ∨ p811)
    (h4660 : p807 ∨ p811)
    (h4665 : p808 ∨ p811)
    (h4553 : p796 ∨ p801 ∨ (¬ p804) ∨ (¬ p805) ∨ (¬ p806) ∨ (¬ p807) ∨ (¬ p808)) : p811 ∨ p796 ∨ p801 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p811) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p796) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p801) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p804 := by
    rcases h4645 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p805 := by
    rcases h4650 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p806 := by
    rcases h4655 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p807 := by
    rcases h4660 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p808 := by
    rcases h4665 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4553 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20727 (p796 p801 p804 p805 p806 p807 p808 p812 : Prop)
    (h4646 : p804 ∨ p812)
    (h4651 : p805 ∨ p812)
    (h4656 : p806 ∨ p812)
    (h4661 : p807 ∨ p812)
    (h4666 : p808 ∨ p812)
    (h4553 : p796 ∨ p801 ∨ (¬ p804) ∨ (¬ p805) ∨ (¬ p806) ∨ (¬ p807) ∨ (¬ p808)) : p812 ∨ p796 ∨ p801 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p812) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p796) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p801) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p804 := by
    rcases h4646 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p805 := by
    rcases h4651 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p806 := by
    rcases h4656 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p807 := by
    rcases h4661 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p808 := by
    rcases h4666 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4553 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20728 (p796 p801 p804 p805 p806 p807 p808 p809 p810 p811 p812 p813 : Prop)
    (h4578 : p796 ∨ p801 ∨ (¬ p809) ∨ (¬ p810) ∨ (¬ p811) ∨ (¬ p812) ∨ (¬ p813))
    (h4647 : p804 ∨ p813)
    (h4652 : p805 ∨ p813)
    (h4657 : p806 ∨ p813)
    (h4662 : p807 ∨ p813)
    (h4667 : p808 ∨ p813)
    (h4553 : p796 ∨ p801 ∨ (¬ p804) ∨ (¬ p805) ∨ (¬ p806) ∨ (¬ p807) ∨ (¬ p808)) : (¬ p812) ∨ (¬ p811) ∨ p801 ∨ p796 ∨ (¬ p809) ∨ (¬ p810) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p812 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p811 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p801) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p796) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p809 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p810 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p813) := by
    rcases h4578 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p804 := by
    rcases h4647 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p805 := by
    rcases h4652 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p806 := by
    rcases h4657 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p807 := by
    rcases h4662 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p808 := by
    rcases h4667 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h4553 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20729 (p796 p801 p809 p810 p811 p812 : Prop)
    (h20724 : p809 ∨ p796 ∨ p801)
    (h20725 : p810 ∨ p796 ∨ p801)
    (h20726 : p811 ∨ p796 ∨ p801)
    (h20727 : p812 ∨ p796 ∨ p801)
    (h20728 : (¬ p812) ∨ (¬ p811) ∨ p801 ∨ p796 ∨ (¬ p809) ∨ (¬ p810)) : p796 ∨ p801 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p796) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p801) := fun hu => hn (Or.inr hu)
  have u2 : p809 := by
    rcases h20724 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p810 := by
    rcases h20725 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p811 := by
    rcases h20726 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p812 := by
    rcases h20727 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20728 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20730 (p790 p814 p823 p824 p825 p826 p827 p828 : Prop)
    (h4769 : p823 ∨ p828)
    (h4774 : p824 ∨ p828)
    (h4779 : p825 ∨ p828)
    (h4784 : p826 ∨ p828)
    (h4789 : p827 ∨ p828)
    (h4681 : p790 ∨ p814 ∨ (¬ p823) ∨ (¬ p824) ∨ (¬ p825) ∨ (¬ p826) ∨ (¬ p827)) : p828 ∨ p790 ∨ p814 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p828) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p790) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p814) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p823 := by
    rcases h4769 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p824 := by
    rcases h4774 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p825 := by
    rcases h4779 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p826 := by
    rcases h4784 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p827 := by
    rcases h4789 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4681 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20731 (p790 p814 p823 p824 p825 p826 p827 p829 : Prop)
    (h4770 : p823 ∨ p829)
    (h4775 : p824 ∨ p829)
    (h4780 : p825 ∨ p829)
    (h4785 : p826 ∨ p829)
    (h4790 : p827 ∨ p829)
    (h4681 : p790 ∨ p814 ∨ (¬ p823) ∨ (¬ p824) ∨ (¬ p825) ∨ (¬ p826) ∨ (¬ p827)) : p829 ∨ p790 ∨ p814 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p829) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p790) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p814) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p823 := by
    rcases h4770 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p824 := by
    rcases h4775 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p825 := by
    rcases h4780 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p826 := by
    rcases h4785 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p827 := by
    rcases h4790 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4681 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20732 (p790 p814 p823 p824 p825 p826 p827 p830 : Prop)
    (h4771 : p823 ∨ p830)
    (h4776 : p824 ∨ p830)
    (h4781 : p825 ∨ p830)
    (h4786 : p826 ∨ p830)
    (h4791 : p827 ∨ p830)
    (h4681 : p790 ∨ p814 ∨ (¬ p823) ∨ (¬ p824) ∨ (¬ p825) ∨ (¬ p826) ∨ (¬ p827)) : p830 ∨ p790 ∨ p814 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p830) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p790) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p814) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p823 := by
    rcases h4771 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p824 := by
    rcases h4776 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p825 := by
    rcases h4781 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p826 := by
    rcases h4786 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p827 := by
    rcases h4791 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4681 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20733 (p790 p814 p823 p824 p825 p826 p827 p831 : Prop)
    (h4772 : p823 ∨ p831)
    (h4777 : p824 ∨ p831)
    (h4782 : p825 ∨ p831)
    (h4787 : p826 ∨ p831)
    (h4792 : p827 ∨ p831)
    (h4681 : p790 ∨ p814 ∨ (¬ p823) ∨ (¬ p824) ∨ (¬ p825) ∨ (¬ p826) ∨ (¬ p827)) : p831 ∨ p790 ∨ p814 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p831) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p790) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p814) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p823 := by
    rcases h4772 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p824 := by
    rcases h4777 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p825 := by
    rcases h4782 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p826 := by
    rcases h4787 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p827 := by
    rcases h4792 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4681 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20734 (p790 p814 p823 p824 p825 p826 p827 p828 p829 p830 p831 p832 : Prop)
    (h4706 : p790 ∨ p814 ∨ (¬ p828) ∨ (¬ p829) ∨ (¬ p830) ∨ (¬ p831) ∨ (¬ p832))
    (h4773 : p823 ∨ p832)
    (h4778 : p824 ∨ p832)
    (h4783 : p825 ∨ p832)
    (h4788 : p826 ∨ p832)
    (h4793 : p827 ∨ p832)
    (h4681 : p790 ∨ p814 ∨ (¬ p823) ∨ (¬ p824) ∨ (¬ p825) ∨ (¬ p826) ∨ (¬ p827)) : (¬ p831) ∨ (¬ p830) ∨ p814 ∨ p790 ∨ (¬ p828) ∨ (¬ p829) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p831 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p830 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p814) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p828 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p829 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p832) := by
    rcases h4706 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p823 := by
    rcases h4773 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p824 := by
    rcases h4778 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p825 := by
    rcases h4783 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p826 := by
    rcases h4788 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p827 := by
    rcases h4793 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h4681 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20735 (p790 p814 p828 p829 p830 p831 : Prop)
    (h20730 : p828 ∨ p790 ∨ p814)
    (h20731 : p829 ∨ p790 ∨ p814)
    (h20732 : p830 ∨ p790 ∨ p814)
    (h20733 : p831 ∨ p790 ∨ p814)
    (h20734 : (¬ p831) ∨ (¬ p830) ∨ p814 ∨ p790 ∨ (¬ p828) ∨ (¬ p829)) : p790 ∨ p814 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p790) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p814) := fun hu => hn (Or.inr hu)
  have u2 : p828 := by
    rcases h20730 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p829 := by
    rcases h20731 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p830 := by
    rcases h20732 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p831 := by
    rcases h20733 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20734 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20736 (p536 p769 p778 p779 p780 p781 p782 p783 : Prop)
    (h4507 : p778 ∨ p783)
    (h4512 : p779 ∨ p783)
    (h4517 : p780 ∨ p783)
    (h4522 : p781 ∨ p783)
    (h4527 : p782 ∨ p783)
    (h4419 : p536 ∨ p769 ∨ (¬ p778) ∨ (¬ p779) ∨ (¬ p780) ∨ (¬ p781) ∨ (¬ p782)) : p783 ∨ p769 ∨ p536 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p783) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p769) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p536) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p778 := by
    rcases h4507 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p779 := by
    rcases h4512 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p780 := by
    rcases h4517 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p781 := by
    rcases h4522 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p782 := by
    rcases h4527 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4419 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20737 (p536 p769 p778 p779 p780 p781 p782 p784 : Prop)
    (h4508 : p778 ∨ p784)
    (h4513 : p779 ∨ p784)
    (h4518 : p780 ∨ p784)
    (h4523 : p781 ∨ p784)
    (h4528 : p782 ∨ p784)
    (h4419 : p536 ∨ p769 ∨ (¬ p778) ∨ (¬ p779) ∨ (¬ p780) ∨ (¬ p781) ∨ (¬ p782)) : p784 ∨ p769 ∨ p536 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p784) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p769) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p536) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p778 := by
    rcases h4508 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p779 := by
    rcases h4513 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p780 := by
    rcases h4518 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p781 := by
    rcases h4523 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p782 := by
    rcases h4528 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4419 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20738 (p536 p769 p778 p779 p780 p781 p782 p785 : Prop)
    (h4509 : p778 ∨ p785)
    (h4514 : p779 ∨ p785)
    (h4519 : p780 ∨ p785)
    (h4524 : p781 ∨ p785)
    (h4529 : p782 ∨ p785)
    (h4419 : p536 ∨ p769 ∨ (¬ p778) ∨ (¬ p779) ∨ (¬ p780) ∨ (¬ p781) ∨ (¬ p782)) : p785 ∨ p769 ∨ p536 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p785) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p769) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p536) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p778 := by
    rcases h4509 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p779 := by
    rcases h4514 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p780 := by
    rcases h4519 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p781 := by
    rcases h4524 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p782 := by
    rcases h4529 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4419 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20739 (p536 p769 p778 p779 p780 p781 p782 p786 : Prop)
    (h4510 : p778 ∨ p786)
    (h4515 : p779 ∨ p786)
    (h4520 : p780 ∨ p786)
    (h4525 : p781 ∨ p786)
    (h4530 : p782 ∨ p786)
    (h4419 : p536 ∨ p769 ∨ (¬ p778) ∨ (¬ p779) ∨ (¬ p780) ∨ (¬ p781) ∨ (¬ p782)) : p786 ∨ p769 ∨ p536 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p786) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p769) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p536) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p778 := by
    rcases h4510 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p779 := by
    rcases h4515 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p780 := by
    rcases h4520 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p781 := by
    rcases h4525 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p782 := by
    rcases h4530 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4419 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20740 (p536 p769 p778 p779 p780 p781 p782 p783 p784 p785 p786 p787 : Prop)
    (h4444 : p536 ∨ p769 ∨ (¬ p783) ∨ (¬ p784) ∨ (¬ p785) ∨ (¬ p786) ∨ (¬ p787))
    (h4511 : p778 ∨ p787)
    (h4516 : p779 ∨ p787)
    (h4521 : p780 ∨ p787)
    (h4526 : p781 ∨ p787)
    (h4531 : p782 ∨ p787)
    (h4419 : p536 ∨ p769 ∨ (¬ p778) ∨ (¬ p779) ∨ (¬ p780) ∨ (¬ p781) ∨ (¬ p782)) : (¬ p786) ∨ (¬ p785) ∨ p536 ∨ p769 ∨ (¬ p783) ∨ (¬ p784) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p786 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p785 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p536) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p769) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p783 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p784 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p787) := by
    rcases h4444 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p778 := by
    rcases h4511 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p779 := by
    rcases h4516 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p780 := by
    rcases h4521 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p781 := by
    rcases h4526 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p782 := by
    rcases h4531 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h4419 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20741 (p536 p769 p783 p784 p785 p786 : Prop)
    (h20736 : p783 ∨ p769 ∨ p536)
    (h20737 : p784 ∨ p769 ∨ p536)
    (h20738 : p785 ∨ p769 ∨ p536)
    (h20739 : p786 ∨ p769 ∨ p536)
    (h20740 : (¬ p786) ∨ (¬ p785) ∨ p536 ∨ p769 ∨ (¬ p783) ∨ (¬ p784)) : p769 ∨ p536 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p769) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p536) := fun hu => hn (Or.inr hu)
  have u2 : p783 := by
    rcases h20736 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p784 := by
    rcases h20737 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p785 := by
    rcases h20738 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p786 := by
    rcases h20739 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20740 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20742 (p980 p982 p986 p987 p988 p989 p990 p995 : Prop)
    (h5816 : p986 ∨ p995)
    (h5821 : p987 ∨ p995)
    (h5826 : p988 ∨ p995)
    (h5831 : p989 ∨ p995)
    (h5836 : p990 ∨ p995)
    (h5723 : p980 ∨ p982 ∨ (¬ p986) ∨ (¬ p987) ∨ (¬ p988) ∨ (¬ p989) ∨ (¬ p990)) : p995 ∨ p982 ∨ p980 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p995) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p982) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p980) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p986 := by
    rcases h5816 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p987 := by
    rcases h5821 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p988 := by
    rcases h5826 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p989 := by
    rcases h5831 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p990 := by
    rcases h5836 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5723 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20743 (p980 p982 p986 p987 p988 p989 p990 p991 : Prop)
    (h5812 : p986 ∨ p991)
    (h5817 : p987 ∨ p991)
    (h5822 : p988 ∨ p991)
    (h5827 : p989 ∨ p991)
    (h5832 : p990 ∨ p991)
    (h5723 : p980 ∨ p982 ∨ (¬ p986) ∨ (¬ p987) ∨ (¬ p988) ∨ (¬ p989) ∨ (¬ p990)) : p991 ∨ p982 ∨ p980 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p991) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p982) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p980) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p986 := by
    rcases h5812 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p987 := by
    rcases h5817 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p988 := by
    rcases h5822 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p989 := by
    rcases h5827 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p990 := by
    rcases h5832 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5723 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20744 (p980 p982 p986 p987 p988 p989 p990 p992 : Prop)
    (h5813 : p986 ∨ p992)
    (h5818 : p987 ∨ p992)
    (h5823 : p988 ∨ p992)
    (h5828 : p989 ∨ p992)
    (h5833 : p990 ∨ p992)
    (h5723 : p980 ∨ p982 ∨ (¬ p986) ∨ (¬ p987) ∨ (¬ p988) ∨ (¬ p989) ∨ (¬ p990)) : p992 ∨ p982 ∨ p980 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p992) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p982) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p980) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p986 := by
    rcases h5813 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p987 := by
    rcases h5818 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p988 := by
    rcases h5823 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p989 := by
    rcases h5828 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p990 := by
    rcases h5833 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5723 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20745 (p980 p982 p986 p987 p988 p989 p990 p993 : Prop)
    (h5814 : p986 ∨ p993)
    (h5819 : p987 ∨ p993)
    (h5824 : p988 ∨ p993)
    (h5829 : p989 ∨ p993)
    (h5834 : p990 ∨ p993)
    (h5723 : p980 ∨ p982 ∨ (¬ p986) ∨ (¬ p987) ∨ (¬ p988) ∨ (¬ p989) ∨ (¬ p990)) : p993 ∨ p982 ∨ p980 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p993) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p982) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p980) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p986 := by
    rcases h5814 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p987 := by
    rcases h5819 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p988 := by
    rcases h5824 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p989 := by
    rcases h5829 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p990 := by
    rcases h5834 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5723 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20746 (p980 p982 p986 p987 p988 p989 p990 p991 p992 p993 p994 p995 : Prop)
    (h5748 : p980 ∨ p982 ∨ (¬ p991) ∨ (¬ p992) ∨ (¬ p993) ∨ (¬ p994) ∨ (¬ p995))
    (h5815 : p986 ∨ p994)
    (h5820 : p987 ∨ p994)
    (h5825 : p988 ∨ p994)
    (h5830 : p989 ∨ p994)
    (h5835 : p990 ∨ p994)
    (h5723 : p980 ∨ p982 ∨ (¬ p986) ∨ (¬ p987) ∨ (¬ p988) ∨ (¬ p989) ∨ (¬ p990)) : (¬ p993) ∨ (¬ p992) ∨ p980 ∨ (¬ p991) ∨ p982 ∨ (¬ p995) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p993 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p992 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p991 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p982) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p995 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p994) := by
    rcases h5748 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u4 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u5)
  have u7 : p986 := by
    rcases h5815 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p987 := by
    rcases h5820 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p988 := by
    rcases h5825 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p989 := by
    rcases h5830 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p990 := by
    rcases h5835 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h5723 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20747 (p980 p982 p991 p992 p993 p995 : Prop)
    (h20742 : p995 ∨ p982 ∨ p980)
    (h20743 : p991 ∨ p982 ∨ p980)
    (h20744 : p992 ∨ p982 ∨ p980)
    (h20745 : p993 ∨ p982 ∨ p980)
    (h20746 : (¬ p993) ∨ (¬ p992) ∨ p980 ∨ (¬ p991) ∨ p982 ∨ (¬ p995)) : p982 ∨ p980 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p982) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr hu)
  have u2 : p995 := by
    rcases h20742 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p991 := by
    rcases h20743 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p992 := by
    rcases h20744 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p993 := by
    rcases h20745 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20746 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (u0 q4)
  · exact False.elim (q5 u2)

theorem step20748 (p728 p734 p740 p741 p742 p743 p744 p745 : Prop)
    (h4256 : p740 ∨ p745)
    (h4261 : p741 ∨ p745)
    (h4266 : p742 ∨ p745)
    (h4271 : p743 ∨ p745)
    (h4276 : p744 ∨ p745)
    (h4168 : p728 ∨ p734 ∨ (¬ p740) ∨ (¬ p741) ∨ (¬ p742) ∨ (¬ p743) ∨ (¬ p744)) : p745 ∨ p728 ∨ p734 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p745) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p728) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p734) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p740 := by
    rcases h4256 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p741 := by
    rcases h4261 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p742 := by
    rcases h4266 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p743 := by
    rcases h4271 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p744 := by
    rcases h4276 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4168 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20749 (p728 p734 p740 p741 p742 p743 p744 p746 : Prop)
    (h4257 : p740 ∨ p746)
    (h4262 : p741 ∨ p746)
    (h4267 : p742 ∨ p746)
    (h4272 : p743 ∨ p746)
    (h4277 : p744 ∨ p746)
    (h4168 : p728 ∨ p734 ∨ (¬ p740) ∨ (¬ p741) ∨ (¬ p742) ∨ (¬ p743) ∨ (¬ p744)) : p746 ∨ p728 ∨ p734 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p746) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p728) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p734) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p740 := by
    rcases h4257 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p741 := by
    rcases h4262 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p742 := by
    rcases h4267 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p743 := by
    rcases h4272 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p744 := by
    rcases h4277 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4168 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20750 (p728 p734 p740 p741 p742 p743 p744 p747 : Prop)
    (h4258 : p740 ∨ p747)
    (h4263 : p741 ∨ p747)
    (h4268 : p742 ∨ p747)
    (h4273 : p743 ∨ p747)
    (h4278 : p744 ∨ p747)
    (h4168 : p728 ∨ p734 ∨ (¬ p740) ∨ (¬ p741) ∨ (¬ p742) ∨ (¬ p743) ∨ (¬ p744)) : p747 ∨ p728 ∨ p734 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p747) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p728) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p734) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p740 := by
    rcases h4258 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p741 := by
    rcases h4263 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p742 := by
    rcases h4268 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p743 := by
    rcases h4273 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p744 := by
    rcases h4278 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4168 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20751 (p728 p734 p740 p741 p742 p743 p744 p748 : Prop)
    (h4259 : p740 ∨ p748)
    (h4264 : p741 ∨ p748)
    (h4269 : p742 ∨ p748)
    (h4274 : p743 ∨ p748)
    (h4279 : p744 ∨ p748)
    (h4168 : p728 ∨ p734 ∨ (¬ p740) ∨ (¬ p741) ∨ (¬ p742) ∨ (¬ p743) ∨ (¬ p744)) : p748 ∨ p728 ∨ p734 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p748) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p728) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p734) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p740 := by
    rcases h4259 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p741 := by
    rcases h4264 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p742 := by
    rcases h4269 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p743 := by
    rcases h4274 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p744 := by
    rcases h4279 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4168 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20752 (p728 p734 p740 p741 p742 p743 p744 p745 p746 p747 p748 p749 : Prop)
    (h4193 : p728 ∨ p734 ∨ (¬ p745) ∨ (¬ p746) ∨ (¬ p747) ∨ (¬ p748) ∨ (¬ p749))
    (h4260 : p740 ∨ p749)
    (h4265 : p741 ∨ p749)
    (h4270 : p742 ∨ p749)
    (h4275 : p743 ∨ p749)
    (h4280 : p744 ∨ p749)
    (h4168 : p728 ∨ p734 ∨ (¬ p740) ∨ (¬ p741) ∨ (¬ p742) ∨ (¬ p743) ∨ (¬ p744)) : (¬ p748) ∨ (¬ p747) ∨ p728 ∨ p734 ∨ (¬ p745) ∨ (¬ p746) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p748 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p747 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p728) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p734) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p745 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p746 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p749) := by
    rcases h4193 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p740 := by
    rcases h4260 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p741 := by
    rcases h4265 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p742 := by
    rcases h4270 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p743 := by
    rcases h4275 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p744 := by
    rcases h4280 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h4168 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20753 (p728 p734 p745 p746 p747 p748 : Prop)
    (h20748 : p745 ∨ p728 ∨ p734)
    (h20749 : p746 ∨ p728 ∨ p734)
    (h20750 : p747 ∨ p728 ∨ p734)
    (h20751 : p748 ∨ p728 ∨ p734)
    (h20752 : (¬ p748) ∨ (¬ p747) ∨ p728 ∨ p734 ∨ (¬ p745) ∨ (¬ p746)) : p728 ∨ p734 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p728) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p734) := fun hu => hn (Or.inr hu)
  have u2 : p745 := by
    rcases h20748 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p746 := by
    rcases h20749 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p747 := by
    rcases h20750 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p748 := by
    rcases h20751 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20752 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20755 (p734 p737 p740 p741 p742 p743 p744 p749 : Prop)
    (h4260 : p740 ∨ p749)
    (h4265 : p741 ∨ p749)
    (h4270 : p742 ∨ p749)
    (h4275 : p743 ∨ p749)
    (h4280 : p744 ∨ p749)
    (h4167 : p734 ∨ p737 ∨ (¬ p740) ∨ (¬ p741) ∨ (¬ p742) ∨ (¬ p743) ∨ (¬ p744)) : p749 ∨ p734 ∨ p737 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p749) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p734) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p737) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p740 := by
    rcases h4260 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p741 := by
    rcases h4265 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p742 := by
    rcases h4270 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p743 := by
    rcases h4275 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p744 := by
    rcases h4280 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4167 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

#print axioms step20755

end NineRUPTrial
