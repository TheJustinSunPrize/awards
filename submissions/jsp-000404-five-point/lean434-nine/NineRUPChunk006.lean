import Mathlib.Tactic.Tauto

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineRUPTrial

theorem step19654 (p7 p434 p435 p601 p996 p1135 p1160 : Prop)
    (h16152 : (¬ p7))
    (h6744 : p1135)
    (h16265 : (¬ p1160))
    (h15067 : p7 ∨ (¬ p434) ∨ (¬ p435) ∨ (¬ p601) ∨ (¬ p996) ∨ (¬ p1135) ∨ p1160) : (¬ p434) ∨ (¬ p435) ∨ (¬ p601) ∨ (¬ p996) := by
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
  have u2 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p1135 := by
    exact h6744
  have u6 : (¬ p1160) := by
    exact h16265
  rcases h15067 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)

theorem step19657 (p7 p10 p121 p122 p577 p601 p918 p980 p1115 p1324 : Prop)
    (h16152 : (¬ p7))
    (h10260 : p122)
    (h16309 : (¬ p1324))
    (h15070 : p7 ∨ (¬ p10) ∨ (¬ p121) ∨ (¬ p122) ∨ (¬ p577) ∨ (¬ p601) ∨ (¬ p918) ∨ (¬ p980) ∨ (¬ p1115) ∨ p1324) : (¬ p10) ∨ (¬ p121) ∨ (¬ p577) ∨ (¬ p601) ∨ (¬ p918) ∨ (¬ p980) ∨ (¬ p1115) := by
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
  have u2 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p918 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p122 := by
    exact h10260
  have u9 : (¬ p1324) := by
    exact h16309
  rcases h15070 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (u9 q9)

theorem step19658 (p7 p10 p25 p121 p290 p601 p885 p1055 p1078 p1102 p1116 : Prop)
    (h16152 : (¬ p7))
    (h15071 : p7 ∨ (¬ p10) ∨ (¬ p25) ∨ (¬ p121) ∨ (¬ p290) ∨ (¬ p601) ∨ (¬ p885) ∨ (¬ p1055) ∨ (¬ p1078) ∨ (¬ p1102) ∨ (¬ p1116)) : (¬ p10) ∨ (¬ p25) ∨ (¬ p121) ∨ (¬ p290) ∨ (¬ p601) ∨ (¬ p885) ∨ (¬ p1055) ∨ (¬ p1078) ∨ (¬ p1102) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p25 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p290 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p885 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1078 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h15071 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19660 (p7 p41 p161 p187 p230 p481 p669 p983 p996 p1099 p1184 p1306 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h7053 : p1184)
    (h15075 : p7 ∨ (¬ p41) ∨ (¬ p161) ∨ (¬ p187) ∨ p230 ∨ (¬ p481) ∨ (¬ p669) ∨ (¬ p983) ∨ (¬ p996) ∨ (¬ p1099) ∨ (¬ p1184) ∨ (¬ p1306)) : (¬ p41) ∨ (¬ p161) ∨ (¬ p187) ∨ (¬ p481) ∨ (¬ p669) ∨ (¬ p983) ∨ (¬ p996) ∨ (¬ p1099) ∨ (¬ p1306) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p230) := by
    exact h16165
  have u11 : p1184 := by
    exact h7053
  rcases h15075 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u10 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u11)
  · exact False.elim (q11 u8)

theorem step19661 (p7 p41 p230 p435 p795 p996 p1022 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6744 : p1135)
    (h15076 : p7 ∨ (¬ p41) ∨ p230 ∨ (¬ p435) ∨ (¬ p795) ∨ (¬ p996) ∨ (¬ p1022) ∨ (¬ p1135)) : (¬ p41) ∨ (¬ p435) ∨ (¬ p795) ∨ (¬ p996) ∨ (¬ p1022) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p795 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p1135 := by
    exact h6744
  rcases h15076 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step19662 (p7 p39 p63 p68 p481 p864 p1002 p1035 p1232 p1269 p1325 : Prop)
    (h16152 : (¬ p7))
    (h15077 : p7 ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p481) ∨ (¬ p864) ∨ (¬ p1002) ∨ (¬ p1035) ∨ (¬ p1232) ∨ (¬ p1269) ∨ (¬ p1325)) : (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p481) ∨ (¬ p864) ∨ (¬ p1002) ∨ (¬ p1035) ∨ (¬ p1232) ∨ (¬ p1269) ∨ (¬ p1325) := by
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
  have u4 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1002 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1035 := by
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
  rcases h15077 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19663 (p7 p39 p68 p88 p185 p481 p985 p996 p1333 p1584 : Prop)
    (h16152 : (¬ p7))
    (h15078 : p7 ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p185) ∨ (¬ p481) ∨ (¬ p985) ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p1584)) : (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p185) ∨ (¬ p481) ∨ (¬ p985) ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p1584) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p68 := by
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
  have u4 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p985 := by
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
  have u8 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15078 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19664 (p7 p68 p426 p481 p537 p836 p885 p996 p1333 p1386 p1538 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h8348 : p1386)
    (h15079 : p7 ∨ (¬ p68) ∨ p426 ∨ (¬ p481) ∨ (¬ p537) ∨ (¬ p836) ∨ (¬ p885) ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p1386) ∨ (¬ p1538)) : (¬ p68) ∨ (¬ p481) ∨ (¬ p537) ∨ (¬ p836) ∨ (¬ p885) ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p1538) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p885 := by
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
  have u7 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p426) := by
    exact h16178
  have u10 : p1386 := by
    exact h8348
  rcases h15079 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19665 (p7 p10 p121 p133 p211 p362 p1386 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h8348 : p1386)
    (h15080 : p7 ∨ (¬ p10) ∨ (¬ p121) ∨ p133 ∨ (¬ p211) ∨ (¬ p362) ∨ (¬ p1386) ∨ (¬ p1452)) : (¬ p10) ∨ (¬ p121) ∨ (¬ p211) ∨ (¬ p362) ∨ (¬ p1452) := by
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
  have u2 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p133) := by
    exact h16157
  have u7 : p1386 := by
    exact h8348
  rcases h15080 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step19666 (p7 p10 p39 p63 p68 p121 p211 p362 p464 p1232 : Prop)
    (h16152 : (¬ p7))
    (h15081 : p7 ∨ (¬ p10) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p121) ∨ (¬ p211) ∨ (¬ p362) ∨ (¬ p464) ∨ (¬ p1232)) : (¬ p10) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p121) ∨ (¬ p211) ∨ (¬ p362) ∨ (¬ p464) ∨ (¬ p1232) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
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
  have u4 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p464 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15081 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19667 (p7 p70 p83 p121 p127 p185 p928 p1249 p1442 : Prop)
    (h16152 : (¬ p7))
    (h15082 : p7 ∨ (¬ p70) ∨ (¬ p83) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p185) ∨ (¬ p928) ∨ (¬ p1249) ∨ (¬ p1442)) : (¬ p70) ∨ (¬ p83) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p185) ∨ (¬ p928) ∨ (¬ p1249) ∨ (¬ p1442) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1442 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15082 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19668 (p7 p70 p85 p426 p481 p836 p918 p996 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h8348 : p1386)
    (h15083 : p7 ∨ (¬ p70) ∨ (¬ p85) ∨ p426 ∨ (¬ p481) ∨ (¬ p836) ∨ (¬ p918) ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p70) ∨ (¬ p85) ∨ (¬ p481) ∨ (¬ p836) ∨ (¬ p918) ∨ (¬ p996) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p836 := by
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
  rcases h15083 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19669 (p7 p70 p83 p185 p481 p928 p996 p1333 p1385 p1386 p1527 : Prop)
    (h16152 : (¬ p7))
    (h8348 : p1386)
    (h16359 : (¬ p1527))
    (h15084 : p7 ∨ (¬ p70) ∨ (¬ p83) ∨ (¬ p185) ∨ (¬ p481) ∨ (¬ p928) ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p1385) ∨ (¬ p1386) ∨ p1527) : (¬ p70) ∨ (¬ p83) ∨ (¬ p185) ∨ (¬ p481) ∨ (¬ p928) ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p928 := by
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
  have u7 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p1386 := by
    exact h8348
  have u10 : (¬ p1527) := by
    exact h16359
  rcases h15084 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u9)
  · exact False.elim (u10 q10)

theorem step19672 (p7 p107 p287 p301 p342 p537 p940 : Prop)
    (h16152 : (¬ p7))
    (h15090 : p7 ∨ (¬ p107) ∨ (¬ p287) ∨ (¬ p301) ∨ (¬ p342) ∨ (¬ p537) ∨ (¬ p940)) : (¬ p107) ∨ (¬ p287) ∨ (¬ p301) ∨ (¬ p342) ∨ (¬ p537) ∨ (¬ p940) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p342 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15090 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19673 (p7 p14 p18 p107 p125 p210 p342 : Prop)
    (h16152 : (¬ p7))
    (h15091 : p7 ∨ (¬ p14) ∨ (¬ p18) ∨ (¬ p107) ∨ (¬ p125) ∨ (¬ p210) ∨ (¬ p342)) : (¬ p14) ∨ (¬ p18) ∨ (¬ p107) ∨ (¬ p125) ∨ (¬ p210) ∨ (¬ p342) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p342 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15091 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19674 (p7 p72 p121 p127 p229 p983 p1037 p1081 p1465 : Prop)
    (h16152 : (¬ p7))
    (h15092 : p7 ∨ (¬ p72) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p229) ∨ (¬ p983) ∨ (¬ p1037) ∨ (¬ p1081) ∨ (¬ p1465)) : (¬ p72) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p229) ∨ (¬ p983) ∨ (¬ p1037) ∨ (¬ p1081) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p72 := by
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
  have u3 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1037 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15092 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19676 (p3 p7 p109 p125 p206 p323 : Prop)
    (h16152 : (¬ p7))
    (h15094 : (¬ p3) ∨ p7 ∨ (¬ p109) ∨ (¬ p125) ∨ (¬ p206) ∨ (¬ p323)) : (¬ p3) ∨ (¬ p109) ∨ (¬ p125) ∨ (¬ p206) ∨ (¬ p323) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15094 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19677 (p6 p7 p140 p191 p301 p303 p424 p476 p687 p1334 : Prop)
    (h16152 : (¬ p7))
    (h15095 : (¬ p6) ∨ p7 ∨ (¬ p140) ∨ (¬ p191) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p424) ∨ (¬ p476) ∨ (¬ p687) ∨ (¬ p1334)) : (¬ p6) ∨ (¬ p140) ∨ (¬ p191) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p424) ∨ (¬ p476) ∨ (¬ p687) ∨ (¬ p1334) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p476 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15095 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19678 (p7 p458 p499 p633 p1080 p1232 : Prop)
    (h16152 : (¬ p7))
    (h15096 : p7 ∨ (¬ p458) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p1080) ∨ (¬ p1232)) : (¬ p458) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p1080) ∨ (¬ p1232) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p458 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15096 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19679 (p7 p167 p189 p406 p817 p940 p985 p1333 : Prop)
    (h16152 : (¬ p7))
    (h15098 : p7 ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p406) ∨ (¬ p817) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1333)) : (¬ p167) ∨ (¬ p189) ∨ (¬ p406) ∨ (¬ p817) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p817 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15098 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19680 (p7 p124 p125 p280 p344 p657 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16173 : (¬ p280))
    (h6744 : p1135)
    (h15099 : p7 ∨ (¬ p124) ∨ (¬ p125) ∨ p280 ∨ (¬ p344) ∨ (¬ p657) ∨ (¬ p1135)) : (¬ p124) ∨ (¬ p125) ∨ (¬ p344) ∨ (¬ p657) := by
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
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p280) := by
    exact h16173
  have u6 : p1135 := by
    exact h6744
  rcases h15099 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19681 (p6 p7 p45 p192 p792 p1207 p1445 p1452 p1465 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16350 : (¬ p1445))
    (h15101 : (¬ p6) ∨ p7 ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p792) ∨ (¬ p1207) ∨ p1445 ∨ (¬ p1452) ∨ (¬ p1465)) : (¬ p6) ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p1207) ∨ (¬ p1452) ∨ (¬ p1465) := by
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
  have u2 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : p792 := by
    exact h4535
  have u8 : (¬ p1445) := by
    exact h16350
  rcases h15101 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u3)
  · exact False.elim (u8 q6)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step19682 (p6 p7 p101 p659 p980 p1076 p1324 : Prop)
    (h16152 : (¬ p7))
    (h3753 : p659)
    (h16309 : (¬ p1324))
    (h15102 : (¬ p6) ∨ p7 ∨ (¬ p101) ∨ (¬ p659) ∨ (¬ p980) ∨ (¬ p1076) ∨ p1324) : (¬ p6) ∨ (¬ p101) ∨ (¬ p980) ∨ (¬ p1076) := by
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
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p659 := by
    exact h3753
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h15102 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step19683 (p7 p69 p983 p1141 p1181 p1184 p1465 : Prop)
    (h16152 : (¬ p7))
    (h16272 : (¬ p1181))
    (h7053 : p1184)
    (h15104 : p7 ∨ (¬ p69) ∨ (¬ p983) ∨ (¬ p1141) ∨ p1181 ∨ (¬ p1184) ∨ (¬ p1465)) : (¬ p69) ∨ (¬ p983) ∨ (¬ p1141) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
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
  have u3 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p1181) := by
    exact h16272
  have u6 : p1184 := by
    exact h7053
  rcases h15104 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step19684 (p7 p41 p63 p616 p799 p1388 : Prop)
    (h16152 : (¬ p7))
    (h15107 : p7 ∨ (¬ p41) ∨ (¬ p63) ∨ (¬ p616) ∨ (¬ p799) ∨ (¬ p1388)) : (¬ p41) ∨ (¬ p63) ∨ (¬ p616) ∨ (¬ p799) ∨ (¬ p1388) := by
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
  have u2 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p799 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1388 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15107 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19685 (p7 p194 p226 p790 p980 p1022 p1036 p1330 : Prop)
    (h16152 : (¬ p7))
    (h15108 : p7 ∨ (¬ p194) ∨ (¬ p226) ∨ (¬ p790) ∨ (¬ p980) ∨ (¬ p1022) ∨ (¬ p1036) ∨ (¬ p1330)) : (¬ p194) ∨ (¬ p226) ∨ (¬ p790) ∨ (¬ p980) ∨ (¬ p1022) ∨ (¬ p1036) ∨ (¬ p1330) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15108 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19686 (p7 p161 p230 p814 p983 p1120 p1184 p1232 p1346 p1393 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h7053 : p1184)
    (h15110 : p7 ∨ (¬ p161) ∨ p230 ∨ (¬ p814) ∨ (¬ p983) ∨ (¬ p1120) ∨ (¬ p1184) ∨ (¬ p1232) ∨ (¬ p1346) ∨ (¬ p1393)) : (¬ p161) ∨ (¬ p814) ∨ (¬ p983) ∨ (¬ p1120) ∨ (¬ p1232) ∨ (¬ p1346) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p230) := by
    exact h16165
  have u9 : p1184 := by
    exact h7053
  rcases h15110 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u8 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step19687 (p7 p86 p161 p389 p789 p790 p1232 p1452 : Prop)
    (h16152 : (¬ p7))
    (h15111 : p7 ∨ (¬ p86) ∨ (¬ p161) ∨ (¬ p389) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1232) ∨ (¬ p1452)) : (¬ p86) ∨ (¬ p161) ∨ (¬ p389) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1232) ∨ (¬ p1452) := by
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
  have u2 : p389 := by
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
  rcases h15111 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19688 (p7 p64 p226 p426 p897 p1036 p1095 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h7053 : p1184)
    (h15113 : p7 ∨ (¬ p64) ∨ (¬ p226) ∨ p426 ∨ (¬ p897) ∨ (¬ p1036) ∨ (¬ p1095) ∨ (¬ p1184)) : (¬ p64) ∨ (¬ p226) ∨ (¬ p897) ∨ (¬ p1036) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p426) := by
    exact h16178
  have u7 : p1184 := by
    exact h7053
  rcases h15113 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step19689 (p7 p41 p42 p166 p918 p980 p1036 p1324 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16309 : (¬ p1324))
    (h15115 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p166) ∨ (¬ p918) ∨ (¬ p980) ∨ (¬ p1036) ∨ p1324) : (¬ p41) ∨ (¬ p166) ∨ (¬ p918) ∨ (¬ p980) ∨ (¬ p1036) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p166 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p1324) := by
    exact h16309
  rcases h15115 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step19690 (p5 p7 p63 p226 p285 p928 p1036 p1077 : Prop)
    (h16152 : (¬ p7))
    (h15116 : (¬ p5) ∨ p7 ∨ (¬ p63) ∨ (¬ p226) ∨ (¬ p285) ∨ (¬ p928) ∨ (¬ p1036) ∨ (¬ p1077)) : (¬ p5) ∨ (¬ p63) ∨ (¬ p226) ∨ (¬ p285) ∨ (¬ p928) ∨ (¬ p1036) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p226 := by
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
  have u5 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15116 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19691 (p7 p41 p42 p137 p532 p576 p1206 p1324 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16309 : (¬ p1324))
    (h15117 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p137) ∨ (¬ p532) ∨ (¬ p576) ∨ (¬ p1206) ∨ p1324) : (¬ p41) ∨ (¬ p137) ∨ (¬ p532) ∨ (¬ p576) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p137 := by
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
  have u4 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p1324) := by
    exact h16309
  rcases h15117 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step19693 (p7 p23 p102 p306 p406 p594 p680 p1287 : Prop)
    (h16152 : (¬ p7))
    (h15119 : p7 ∨ (¬ p23) ∨ (¬ p102) ∨ (¬ p306) ∨ (¬ p406) ∨ (¬ p594) ∨ (¬ p680) ∨ (¬ p1287)) : (¬ p23) ∨ (¬ p102) ∨ (¬ p306) ∨ (¬ p406) ∨ (¬ p594) ∨ (¬ p680) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p594 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15119 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19694 (p6 p7 p45 p90 p101 p192 p237 p657 p686 p840 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h6744 : p1135)
    (h15120 : (¬ p6) ∨ p7 ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p101) ∨ (¬ p192) ∨ (¬ p237) ∨ (¬ p657) ∨ p686 ∨ (¬ p840) ∨ (¬ p1135)) : (¬ p6) ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p101) ∨ (¬ p192) ∨ (¬ p237) ∨ (¬ p657) ∨ (¬ p840) := by
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
  have u4 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p686) := by
    exact h16205
  have u10 : p1135 := by
    exact h6744
  rcases h15120 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (u9 q8)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u10)

theorem step19695 (p7 p15 p21 p101 p128 p346 p426 p495 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16178 : (¬ p426))
    (h15121 : p7 ∨ (¬ p15) ∨ (¬ p21) ∨ (¬ p101) ∨ (¬ p128) ∨ (¬ p346) ∨ p426 ∨ (¬ p495)) : (¬ p15) ∨ (¬ p21) ∨ (¬ p101) ∨ (¬ p346) ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p21 := by
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
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p128 := by
    exact h653
  have u7 : (¬ p426) := by
    exact h16178
  rcases h15121 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step19696 (p6 p7 p38 p49 p84 p237 p389 p657 p840 p1206 : Prop)
    (h16152 : (¬ p7))
    (h15124 : (¬ p6) ∨ p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p237) ∨ (¬ p389) ∨ (¬ p657) ∨ (¬ p840) ∨ (¬ p1206)) : (¬ p6) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p237) ∨ (¬ p389) ∨ (¬ p657) ∨ (¬ p840) ∨ (¬ p1206) := by
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
  have u4 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15124 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19697 (p7 p8 p15 p49 p84 p242 p431 p616 p657 p1545 : Prop)
    (h16152 : (¬ p7))
    (h15125 : p7 ∨ (¬ p8) ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p242) ∨ (¬ p431) ∨ (¬ p616) ∨ (¬ p657) ∨ (¬ p1545)) : (¬ p8) ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p242) ∨ (¬ p431) ∨ (¬ p616) ∨ (¬ p657) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p15 := by
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
  have u4 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15125 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19698 (p7 p728 p834 p904 p917 p1015 : Prop)
    (h16152 : (¬ p7))
    (h15126 : p7 ∨ (¬ p728) ∨ (¬ p834) ∨ (¬ p904) ∨ (¬ p917) ∨ (¬ p1015)) : (¬ p728) ∨ (¬ p834) ∨ (¬ p904) ∨ (¬ p917) ∨ (¬ p1015) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p834 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p917 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15126 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19700 (p7 p8 p420 p431 p438 p495 p657 p1100 : Prop)
    (h16152 : (¬ p7))
    (h15128 : p7 ∨ (¬ p8) ∨ (¬ p420) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p495) ∨ (¬ p657) ∨ (¬ p1100)) : (¬ p8) ∨ (¬ p420) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p495) ∨ (¬ p657) ∨ (¬ p1100) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p438 := by
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
  have u6 : p1100 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15128 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19701 (p6 p7 p19 p156 p185 p192 p229 p653 p789 p790 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16194 : (¬ p653))
    (h6744 : p1135)
    (h15129 : (¬ p6) ∨ p7 ∨ (¬ p19) ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p192) ∨ (¬ p229) ∨ p653 ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1135)) : (¬ p6) ∨ (¬ p19) ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p192) ∨ (¬ p229) ∨ (¬ p789) ∨ (¬ p790) := by
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
  have u2 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p229 := by
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
  have u9 : (¬ p653) := by
    exact h16194
  have u10 : p1135 := by
    exact h6744
  rcases h15129 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u9 q7)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u10)

theorem step19702 (p7 p158 p230 p657 p680 p687 p734 p928 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6744 : p1135)
    (h15130 : p7 ∨ (¬ p158) ∨ p230 ∨ (¬ p657) ∨ (¬ p680) ∨ (¬ p687) ∨ (¬ p734) ∨ (¬ p928) ∨ (¬ p1135)) : (¬ p158) ∨ (¬ p657) ∨ (¬ p680) ∨ (¬ p687) ∨ (¬ p734) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p230) := by
    exact h16165
  have u8 : p1135 := by
    exact h6744
  rcases h15130 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u8)

theorem step19703 (p7 p18 p69 p349 p389 p406 p434 p686 p690 p1184 p1206 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h7053 : p1184)
    (h15132 : p7 ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p349) ∨ (¬ p389) ∨ (¬ p406) ∨ (¬ p434) ∨ p686 ∨ (¬ p690) ∨ (¬ p1184) ∨ (¬ p1206)) : (¬ p18) ∨ (¬ p69) ∨ (¬ p349) ∨ (¬ p389) ∨ (¬ p406) ∨ (¬ p434) ∨ (¬ p690) ∨ (¬ p1206) := by
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
  have u2 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p686) := by
    exact h16205
  have u10 : p1184 := by
    exact h7053
  rcases h15132 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u9 q7)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u10)
  · exact False.elim (q10 u7)

theorem step19704 (p7 p10 p18 p69 p430 p438 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16180 : (¬ p430))
    (h7053 : p1184)
    (h15133 : p7 ∨ (¬ p10) ∨ (¬ p18) ∨ (¬ p69) ∨ p430 ∨ (¬ p438) ∨ (¬ p1184)) : (¬ p10) ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p438) := by
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
  have u3 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p430) := by
    exact h16180
  have u6 : p1184 := by
    exact h7053
  rcases h15133 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19705 (p7 p237 p285 p344 p814 p835 : Prop)
    (h16152 : (¬ p7))
    (h15134 : p7 ∨ (¬ p237) ∨ (¬ p285) ∨ (¬ p344) ∨ (¬ p814) ∨ (¬ p835)) : (¬ p237) ∨ (¬ p285) ∨ (¬ p344) ∨ (¬ p814) ∨ (¬ p835) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p285 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
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
  rcases h15134 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19706 (p7 p85 p620 p687 p1394 p1545 : Prop)
    (h16152 : (¬ p7))
    (h15135 : p7 ∨ (¬ p85) ∨ (¬ p620) ∨ (¬ p687) ∨ (¬ p1394) ∨ (¬ p1545)) : (¬ p85) ∨ (¬ p620) ∨ (¬ p687) ∨ (¬ p1394) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p620 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1394 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15135 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19707 (p6 p7 p101 p194 p346 p426 p687 p789 p820 p1015 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h6744 : p1135)
    (h15136 : (¬ p6) ∨ p7 ∨ (¬ p101) ∨ (¬ p194) ∨ (¬ p346) ∨ p426 ∨ (¬ p687) ∨ (¬ p789) ∨ (¬ p820) ∨ (¬ p1015) ∨ (¬ p1135)) : (¬ p6) ∨ (¬ p101) ∨ (¬ p194) ∨ (¬ p346) ∨ (¬ p687) ∨ (¬ p789) ∨ (¬ p820) ∨ (¬ p1015) := by
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
  have u4 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p820 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p426) := by
    exact h16178
  have u10 : p1135 := by
    exact h6744
  rcases h15136 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u9 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u10)

theorem step19708 (p7 p64 p185 p230 p928 p1159 p1184 p1346 p1452 p1465 p1490 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h7053 : p1184)
    (h15137 : p7 ∨ (¬ p64) ∨ (¬ p185) ∨ p230 ∨ (¬ p928) ∨ (¬ p1159) ∨ (¬ p1184) ∨ (¬ p1346) ∨ (¬ p1452) ∨ (¬ p1465) ∨ (¬ p1490)) : (¬ p64) ∨ (¬ p185) ∨ (¬ p928) ∨ (¬ p1159) ∨ (¬ p1346) ∨ (¬ p1452) ∨ (¬ p1465) ∨ (¬ p1490) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1490 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p230) := by
    exact h16165
  have u10 : p1184 := by
    exact h7053
  rcases h15137 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u9 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step19709 (p7 p15 p128 p161 p1232 p1445 p1452 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16350 : (¬ p1445))
    (h15138 : p7 ∨ (¬ p15) ∨ (¬ p128) ∨ (¬ p161) ∨ (¬ p1232) ∨ p1445 ∨ (¬ p1452)) : (¬ p15) ∨ (¬ p161) ∨ (¬ p1232) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p128 := by
    exact h653
  have u6 : (¬ p1445) := by
    exact h16350
  rcases h15138 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step19712 (p5 p7 p13 p1095 p1096 p1159 p1452 p1465 : Prop)
    (h16152 : (¬ p7))
    (h15142 : (¬ p5) ∨ p7 ∨ (¬ p13) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1159) ∨ (¬ p1452) ∨ (¬ p1465)) : (¬ p5) ∨ (¬ p13) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1159) ∨ (¬ p1452) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15142 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19713 (p5 p7 p13 p978 p1096 p1159 p1452 p1465 p1562 : Prop)
    (h16152 : (¬ p7))
    (h15143 : (¬ p5) ∨ p7 ∨ (¬ p13) ∨ (¬ p978) ∨ (¬ p1096) ∨ (¬ p1159) ∨ (¬ p1452) ∨ (¬ p1465) ∨ (¬ p1562)) : (¬ p5) ∨ (¬ p13) ∨ (¬ p978) ∨ (¬ p1096) ∨ (¬ p1159) ∨ (¬ p1452) ∨ (¬ p1465) ∨ (¬ p1562) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p978 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15143 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19715 (p7 p285 p344 p406 p656 p834 p858 : Prop)
    (h16152 : (¬ p7))
    (h15146 : p7 ∨ (¬ p285) ∨ (¬ p344) ∨ (¬ p406) ∨ (¬ p656) ∨ (¬ p834) ∨ (¬ p858)) : (¬ p285) ∨ (¬ p344) ∨ (¬ p406) ∨ (¬ p656) ∨ (¬ p834) ∨ (¬ p858) := by
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
  have u2 : p406 := by
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
  rcases h15146 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19716 (p5 p6 p7 p63 p532 p1206 p1512 p1771 : Prop)
    (h16152 : (¬ p7))
    (h15147 : (¬ p5) ∨ (¬ p6) ∨ p7 ∨ (¬ p63) ∨ (¬ p532) ∨ (¬ p1206) ∨ (¬ p1512) ∨ (¬ p1771)) : (¬ p5) ∨ (¬ p6) ∨ (¬ p63) ∨ (¬ p532) ∨ (¬ p1206) ∨ (¬ p1512) ∨ (¬ p1771) := by
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
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1512 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1771 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15147 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19717 (p7 p41 p42 p104 p346 p426 p534 p1586 p1772 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16178 : (¬ p426))
    (h15148 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p104) ∨ (¬ p346) ∨ p426 ∨ (¬ p534) ∨ (¬ p1586) ∨ (¬ p1772)) : (¬ p41) ∨ (¬ p104) ∨ (¬ p346) ∨ (¬ p534) ∨ (¬ p1586) ∨ (¬ p1772) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1586 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1772 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : p42 := by
    exact h132
  have u8 : (¬ p426) := by
    exact h16178
  rcases h15148 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u8 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step19718 (p7 p41 p687 p799 p816 p1387 p1545 : Prop)
    (h16152 : (¬ p7))
    (h15149 : p7 ∨ (¬ p41) ∨ (¬ p687) ∨ (¬ p799) ∨ (¬ p816) ∨ (¬ p1387) ∨ (¬ p1545)) : (¬ p41) ∨ (¬ p687) ∨ (¬ p799) ∨ (¬ p816) ∨ (¬ p1387) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p799 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15149 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19719 (p5 p7 p12 p556 p595 p739 p940 p1055 p1542 : Prop)
    (h16152 : (¬ p7))
    (h15150 : (¬ p5) ∨ p7 ∨ (¬ p12) ∨ (¬ p556) ∨ (¬ p595) ∨ (¬ p739) ∨ (¬ p940) ∨ (¬ p1055) ∨ (¬ p1542)) : (¬ p5) ∨ (¬ p12) ∨ (¬ p556) ∨ (¬ p595) ∨ (¬ p739) ∨ (¬ p940) ∨ (¬ p1055) ∨ (¬ p1542) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p739 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15150 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19720 (p7 p69 p86 p225 p229 p237 p668 p1116 : Prop)
    (h16152 : (¬ p7))
    (h15152 : p7 ∨ (¬ p69) ∨ (¬ p86) ∨ (¬ p225) ∨ (¬ p229) ∨ (¬ p237) ∨ (¬ p668) ∨ (¬ p1116)) : (¬ p69) ∨ (¬ p86) ∨ (¬ p225) ∨ (¬ p229) ∨ (¬ p237) ∨ (¬ p668) ∨ (¬ p1116) := by
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
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15152 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19721 (p7 p69 p86 p224 p545 p789 p790 p1187 : Prop)
    (h16152 : (¬ p7))
    (h15153 : p7 ∨ (¬ p69) ∨ (¬ p86) ∨ (¬ p224) ∨ (¬ p545) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1187)) : (¬ p69) ∨ (¬ p86) ∨ (¬ p224) ∨ (¬ p545) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1187) := by
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
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p545 := by
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
  have u6 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15153 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19722 (p7 p102 p257 p349 p434 p657 p734 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h6744 : p1135)
    (h15154 : p7 ∨ (¬ p102) ∨ p257 ∨ (¬ p349) ∨ (¬ p434) ∨ (¬ p657) ∨ (¬ p734) ∨ (¬ p1135)) : (¬ p102) ∨ (¬ p349) ∨ (¬ p434) ∨ (¬ p657) ∨ (¬ p734) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p257) := by
    exact h16170
  have u7 : p1135 := by
    exact h6744
  rcases h15154 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step19723 (p7 p20 p69 p101 p121 p456 p686 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h7053 : p1184)
    (h15155 : p7 ∨ (¬ p20) ∨ (¬ p69) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p456) ∨ p686 ∨ (¬ p1184)) : (¬ p20) ∨ (¬ p69) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p456) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p20 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p686) := by
    exact h16205
  have u7 : p1184 := by
    exact h7053
  rcases h15155 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u7)

theorem step19724 (p7 p156 p192 p206 p455 p580 p918 p961 : Prop)
    (h16152 : (¬ p7))
    (h15156 : p7 ∨ (¬ p156) ∨ (¬ p192) ∨ (¬ p206) ∨ (¬ p455) ∨ (¬ p580) ∨ (¬ p918) ∨ (¬ p961)) : (¬ p156) ∨ (¬ p192) ∨ (¬ p206) ∨ (¬ p455) ∨ (¬ p580) ∨ (¬ p918) ∨ (¬ p961) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15156 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19725 (p7 p18 p101 p423 p659 p686 p1159 : Prop)
    (h16152 : (¬ p7))
    (h3753 : p659)
    (h16205 : (¬ p686))
    (h15157 : p7 ∨ (¬ p18) ∨ (¬ p101) ∨ (¬ p423) ∨ (¬ p659) ∨ p686 ∨ (¬ p1159)) : (¬ p18) ∨ (¬ p101) ∨ (¬ p423) ∨ (¬ p1159) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p659 := by
    exact h3753
  have u6 : (¬ p686) := by
    exact h16205
  rcases h15157 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step19726 (p7 p10 p18 p69 p224 p351 p406 p617 : Prop)
    (h16152 : (¬ p7))
    (h15158 : p7 ∨ (¬ p10) ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p224) ∨ (¬ p351) ∨ (¬ p406) ∨ (¬ p617)) : (¬ p10) ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p224) ∨ (¬ p351) ∨ (¬ p406) ∨ (¬ p617) := by
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
  have u6 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15158 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19727 (p7 p185 p230 p657 p790 p833 p928 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6744 : p1135)
    (h15159 : p7 ∨ (¬ p185) ∨ p230 ∨ (¬ p657) ∨ (¬ p790) ∨ (¬ p833) ∨ (¬ p928) ∨ (¬ p1135)) : (¬ p185) ∨ (¬ p657) ∨ (¬ p790) ∨ (¬ p833) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p833 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p1135 := by
    exact h6744
  rcases h15159 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step19728 (p7 p103 p121 p206 p225 p344 p659 p686 p961 : Prop)
    (h16152 : (¬ p7))
    (h3753 : p659)
    (h16205 : (¬ p686))
    (h15161 : p7 ∨ (¬ p103) ∨ (¬ p121) ∨ (¬ p206) ∨ (¬ p225) ∨ (¬ p344) ∨ (¬ p659) ∨ p686 ∨ (¬ p961)) : (¬ p103) ∨ (¬ p121) ∨ (¬ p206) ∨ (¬ p225) ∨ (¬ p344) ∨ (¬ p961) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : p659 := by
    exact h3753
  have u8 : (¬ p686) := by
    exact h16205
  rcases h15161 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u7)
  · exact False.elim (u8 q7)
  · exact False.elim (q8 u5)

theorem step19729 (p7 p101 p121 p206 p346 p426 p659 p961 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h3753 : p659)
    (h15162 : p7 ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p206) ∨ (¬ p346) ∨ p426 ∨ (¬ p659) ∨ (¬ p961)) : (¬ p101) ∨ (¬ p121) ∨ (¬ p206) ∨ (¬ p346) ∨ (¬ p961) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p426) := by
    exact h16178
  have u7 : p659 := by
    exact h3753
  rcases h15162 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step19732 (p7 p63 p101 p121 p285 p500 p928 p961 : Prop)
    (h16152 : (¬ p7))
    (h15165 : p7 ∨ (¬ p63) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p285) ∨ (¬ p500) ∨ (¬ p928) ∨ (¬ p961)) : (¬ p63) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p285) ∨ (¬ p500) ∨ (¬ p928) ∨ (¬ p961) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
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
  have u3 : p285 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15165 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19733 (p7 p10 p121 p351 p500 p904 p961 p1096 : Prop)
    (h16152 : (¬ p7))
    (h15166 : p7 ∨ (¬ p10) ∨ (¬ p121) ∨ (¬ p351) ∨ (¬ p500) ∨ (¬ p904) ∨ (¬ p961) ∨ (¬ p1096)) : (¬ p10) ∨ (¬ p121) ∨ (¬ p351) ∨ (¬ p500) ∨ (¬ p904) ∨ (¬ p961) ∨ (¬ p1096) := by
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
  have u2 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15166 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19734 (p7 p41 p42 p101 p121 p237 p267 p686 p918 p961 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16205 : (¬ p686))
    (h15167 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p237) ∨ (¬ p267) ∨ p686 ∨ (¬ p918) ∨ (¬ p961)) : (¬ p41) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p237) ∨ (¬ p267) ∨ (¬ p918) ∨ (¬ p961) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
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
  have u3 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p267 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p42 := by
    exact h132
  have u9 : (¬ p686) := by
    exact h16205
  rcases h15167 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u9 q7)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step19735 (p7 p10 p121 p194 p206 p237 p351 p840 p961 : Prop)
    (h16152 : (¬ p7))
    (h15168 : p7 ∨ (¬ p10) ∨ (¬ p121) ∨ (¬ p194) ∨ (¬ p206) ∨ (¬ p237) ∨ (¬ p351) ∨ (¬ p840) ∨ (¬ p961)) : (¬ p10) ∨ (¬ p121) ∨ (¬ p194) ∨ (¬ p206) ∨ (¬ p237) ∨ (¬ p351) ∨ (¬ p840) ∨ (¬ p961) := by
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
  have u2 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p351 := by
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
  rcases h15168 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19736 (p7 p8 p101 p121 p194 p206 p242 p686 p836 p961 p1116 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h6761 : p1139)
    (h15169 : p7 ∨ (¬ p8) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p194) ∨ (¬ p206) ∨ (¬ p242) ∨ p686 ∨ (¬ p836) ∨ (¬ p961) ∨ (¬ p1116) ∨ (¬ p1139)) : (¬ p8) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p194) ∨ (¬ p206) ∨ (¬ p242) ∨ (¬ p836) ∨ (¬ p961) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
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
  have u3 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p686) := by
    exact h16205
  have u11 : p1139 := by
    exact h6761
  rcases h15169 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u10 q7)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u8)
  · exact False.elim (q11 u11)

theorem step19737 (p7 p15 p49 p769 p927 p1097 p1562 : Prop)
    (h16152 : (¬ p7))
    (h15170 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p769) ∨ (¬ p927) ∨ (¬ p1097) ∨ (¬ p1562)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p769) ∨ (¬ p927) ∨ (¬ p1097) ∨ (¬ p1562) := by
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
  have u2 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1097 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15170 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19738 (p7 p101 p121 p242 p267 p285 p536 p961 p1584 : Prop)
    (h16152 : (¬ p7))
    (h15171 : p7 ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p242) ∨ (¬ p267) ∨ (¬ p285) ∨ (¬ p536) ∨ (¬ p961) ∨ (¬ p1584)) : (¬ p101) ∨ (¬ p121) ∨ (¬ p242) ∨ (¬ p267) ∨ (¬ p285) ∨ (¬ p536) ∨ (¬ p961) ∨ (¬ p1584) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p267 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p285 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15171 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19739 (p2 p7 p194 p237 p419 p533 p537 p1325 : Prop)
    (h16152 : (¬ p7))
    (h15172 : (¬ p2) ∨ p7 ∨ (¬ p194) ∨ (¬ p237) ∨ (¬ p419) ∨ (¬ p533) ∨ (¬ p537) ∨ (¬ p1325)) : (¬ p2) ∨ (¬ p194) ∨ (¬ p237) ∨ (¬ p419) ∨ (¬ p533) ∨ (¬ p537) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15172 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19740 (p7 p101 p224 p323 p343 p364 p406 p686 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16205 : (¬ p686))
    (h15173 : p7 ∨ (¬ p101) ∨ (¬ p224) ∨ (¬ p323) ∨ (¬ p343) ∨ (¬ p364) ∨ (¬ p406) ∨ p686) : (¬ p101) ∨ (¬ p224) ∨ (¬ p323) ∨ (¬ p364) ∨ (¬ p406) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p343 := by
    exact h1950
  have u7 : (¬ p686) := by
    exact h16205
  rcases h15173 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step19741 (p7 p101 p121 p350 p362 p961 : Prop)
    (h16152 : (¬ p7))
    (h15174 : p7 ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p350) ∨ (¬ p362) ∨ (¬ p961)) : (¬ p101) ∨ (¬ p121) ∨ (¬ p350) ∨ (¬ p362) ∨ (¬ p961) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15174 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19742 (p7 p123 p224 p343 p406 p576 p816 p1393 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h1950 : p343)
    (h15176 : p7 ∨ p123 ∨ (¬ p224) ∨ (¬ p343) ∨ (¬ p406) ∨ (¬ p576) ∨ (¬ p816) ∨ (¬ p1393)) : (¬ p224) ∨ (¬ p406) ∨ (¬ p576) ∨ (¬ p816) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p576 := by
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
  have u6 : (¬ p123) := by
    exact h16186
  have u7 : p343 := by
    exact h1950
  rcases h15176 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step19743 (p7 p124 p132 p258 p532 p961 p1324 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16309 : (¬ p1324))
    (h15177 : p7 ∨ (¬ p124) ∨ (¬ p132) ∨ (¬ p258) ∨ (¬ p532) ∨ (¬ p961) ∨ p1324) : (¬ p124) ∨ (¬ p258) ∨ (¬ p532) ∨ (¬ p961) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p132 := by
    exact h786
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h15177 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step19744 (p2 p7 p124 p194 p228 p258 p266 p419 p1443 : Prop)
    (h16152 : (¬ p7))
    (h15178 : (¬ p2) ∨ p7 ∨ (¬ p124) ∨ (¬ p194) ∨ (¬ p228) ∨ (¬ p258) ∨ (¬ p266) ∨ (¬ p419) ∨ (¬ p1443)) : (¬ p2) ∨ (¬ p124) ∨ (¬ p194) ∨ (¬ p228) ∨ (¬ p258) ∨ (¬ p266) ∨ (¬ p419) ∨ (¬ p1443) := by
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
  have u2 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15178 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19745 (p7 p69 p70 p481 p1187 : Prop)
    (h16152 : (¬ p7))
    (h15179 : p7 ∨ (¬ p69) ∨ (¬ p70) ∨ (¬ p481) ∨ (¬ p1187)) : (¬ p69) ∨ (¬ p70) ∨ (¬ p481) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p70 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  rcases h15179 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)

theorem step19746 (p5 p7 p226 p344 p499 p633 p664 p1036 : Prop)
    (h16152 : (¬ p7))
    (h15180 : (¬ p5) ∨ p7 ∨ (¬ p226) ∨ (¬ p344) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p664) ∨ (¬ p1036)) : (¬ p5) ∨ (¬ p226) ∨ (¬ p344) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p664) ∨ (¬ p1036) := by
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
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15180 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19747 (p2 p5 p7 p343 p344 p419 p499 p633 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16309 : (¬ p1324))
    (h15181 : (¬ p2) ∨ (¬ p5) ∨ p7 ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p419) ∨ (¬ p499) ∨ (¬ p633) ∨ p1324 ∨ (¬ p1325)) : (¬ p2) ∨ (¬ p5) ∨ (¬ p344) ∨ (¬ p419) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p343 := by
    exact h1950
  have u9 : (¬ p1324) := by
    exact h16309
  rcases h15181 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u9 q8)
  · exact False.elim (q9 u6)

theorem step19748 (p7 p41 p42 p426 p657 p858 p1385 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16178 : (¬ p426))
    (h15182 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ p426 ∨ (¬ p657) ∨ (¬ p858) ∨ (¬ p1385)) : (¬ p41) ∨ (¬ p657) ∨ (¬ p858) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p657 := by
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
  have u6 : (¬ p426) := by
    exact h16178
  rcases h15182 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19749 (p7 p224 p225 p226 p659 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h3753 : p659)
    (h16309 : (¬ p1324))
    (h15183 : p7 ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p659) ∨ p1324 ∨ (¬ p1325)) : (¬ p224) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p659 := by
    exact h3753
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h15183 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step19750 (p7 p17 p230 p347 p518 p581 p616 p657 p790 p1184 p1287 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h7053 : p1184)
    (h15184 : p7 ∨ (¬ p17) ∨ p230 ∨ (¬ p347) ∨ (¬ p518) ∨ (¬ p581) ∨ (¬ p616) ∨ (¬ p657) ∨ (¬ p790) ∨ (¬ p1184) ∨ (¬ p1287)) : (¬ p17) ∨ (¬ p347) ∨ (¬ p518) ∨ (¬ p581) ∨ (¬ p616) ∨ (¬ p657) ∨ (¬ p790) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p518 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p581 := by
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
  have u6 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p230) := by
    exact h16165
  have u10 : p1184 := by
    exact h7053
  rcases h15184 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19751 (p5 p7 p226 p595 p980 p1036 p1330 p1542 : Prop)
    (h16152 : (¬ p7))
    (h15185 : (¬ p5) ∨ p7 ∨ (¬ p226) ∨ (¬ p595) ∨ (¬ p980) ∨ (¬ p1036) ∨ (¬ p1330) ∨ (¬ p1542)) : (¬ p5) ∨ (¬ p226) ∨ (¬ p595) ∨ (¬ p980) ∨ (¬ p1036) ∨ (¬ p1330) ∨ (¬ p1542) := by
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
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1036 := by
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
  rcases h15185 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19754 (p185 p244 p279 p682 : Prop)
    (h1444 : p279)
    (h16203 : (¬ p682))
    (h15188 : (¬ p185) ∨ p244 ∨ (¬ p279) ∨ p682) : (¬ p185) ∨ p244 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p244) := fun hu => hn (Or.inr hu)
  have u2 : p279 := by
    exact h1444
  have u3 : (¬ p682) := by
    exact h16203
  rcases h15188 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)

theorem step19755 (p7 p303 p521 p814 p861 p1346 : Prop)
    (h16152 : (¬ p7))
    (h15190 : p7 ∨ (¬ p303) ∨ (¬ p521) ∨ (¬ p814) ∨ (¬ p861) ∨ (¬ p1346)) : (¬ p303) ∨ (¬ p521) ∨ (¬ p814) ∨ (¬ p861) ∨ (¬ p1346) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p521 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p814 := by
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
  rcases h15190 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19756 (p7 p17 p123 p128 p789 p790 p1188 p1287 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h653 : p128)
    (h15191 : p7 ∨ (¬ p17) ∨ p123 ∨ (¬ p128) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1188) ∨ (¬ p1287)) : (¬ p17) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1188) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
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
  have u6 : (¬ p123) := by
    exact h16186
  have u7 : p128 := by
    exact h653
  rcases h15191 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step19757 (p7 p162 p303 p406 p427 p537 p680 p769 : Prop)
    (h16152 : (¬ p7))
    (h16160 : (¬ p162))
    (h2334 : p427)
    (h15192 : p7 ∨ p162 ∨ (¬ p303) ∨ (¬ p406) ∨ (¬ p427) ∨ (¬ p537) ∨ (¬ p680) ∨ (¬ p769)) : (¬ p303) ∨ (¬ p406) ∨ (¬ p537) ∨ (¬ p680) ∨ (¬ p769) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p162) := by
    exact h16160
  have u7 : p427 := by
    exact h2334
  rcases h15192 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step19758 (p2 p7 p303 p331 p1001 p1140 : Prop)
    (h16152 : (¬ p7))
    (h15193 : (¬ p2) ∨ p7 ∨ (¬ p303) ∨ (¬ p331) ∨ (¬ p1001) ∨ (¬ p1140)) : (¬ p2) ∨ (¬ p303) ∨ (¬ p331) ∨ (¬ p1001) ∨ (¬ p1140) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p331 := by
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
  rcases h15193 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19759 (p7 p69 p86 p124 p126 p258 p266 p331 p1187 : Prop)
    (h16152 : (¬ p7))
    (h15194 : p7 ∨ (¬ p69) ∨ (¬ p86) ∨ (¬ p124) ∨ (¬ p126) ∨ (¬ p258) ∨ (¬ p266) ∨ (¬ p331) ∨ (¬ p1187)) : (¬ p69) ∨ (¬ p86) ∨ (¬ p124) ∨ (¬ p126) ∨ (¬ p258) ∨ (¬ p266) ∨ (¬ p331) ∨ (¬ p1187) := by
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
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15194 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19760 (p7 p124 p125 p139 p258 p323 : Prop)
    (h16152 : (¬ p7))
    (h15195 : p7 ∨ (¬ p124) ∨ (¬ p125) ∨ (¬ p139) ∨ (¬ p258) ∨ (¬ p323)) : (¬ p124) ∨ (¬ p125) ∨ (¬ p139) ∨ (¬ p258) ∨ (¬ p323) := by
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
  have u2 : p139 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15195 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19761 (p7 p125 p227 p342 p456 p633 : Prop)
    (h16152 : (¬ p7))
    (h15196 : p7 ∨ (¬ p125) ∨ (¬ p227) ∨ (¬ p342) ∨ (¬ p456) ∨ (¬ p633)) : (¬ p125) ∨ (¬ p227) ∨ (¬ p342) ∨ (¬ p456) ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p342 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15196 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19762 (p7 p194 p226 p256 p983 p1037 p1081 p1443 p1465 : Prop)
    (h16152 : (¬ p7))
    (h15197 : p7 ∨ (¬ p194) ∨ (¬ p226) ∨ (¬ p256) ∨ (¬ p983) ∨ (¬ p1037) ∨ (¬ p1081) ∨ (¬ p1443) ∨ (¬ p1465)) : (¬ p194) ∨ (¬ p226) ∨ (¬ p256) ∨ (¬ p983) ∨ (¬ p1037) ∨ (¬ p1081) ∨ (¬ p1443) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p226 := by
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
  have u4 : p1037 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15197 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19763 (p7 p69 p229 p983 p1037 p1181 p1184 p1465 : Prop)
    (h16152 : (¬ p7))
    (h16272 : (¬ p1181))
    (h7053 : p1184)
    (h15198 : p7 ∨ (¬ p69) ∨ (¬ p229) ∨ (¬ p983) ∨ (¬ p1037) ∨ p1181 ∨ (¬ p1184) ∨ (¬ p1465)) : (¬ p69) ∨ (¬ p229) ∨ (¬ p983) ∨ (¬ p1037) ∨ (¬ p1465) := by
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
  have u2 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1037 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p1181) := by
    exact h16272
  have u7 : p1184 := by
    exact h7053
  rcases h15198 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step19764 (p7 p303 p345 p368 p406 p752 p1624 : Prop)
    (h16152 : (¬ p7))
    (h15199 : p7 ∨ (¬ p303) ∨ (¬ p345) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p752) ∨ (¬ p1624)) : (¬ p303) ∨ (¬ p345) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p752) ∨ (¬ p1624) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p752 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15199 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19765 (p7 p17 p230 p303 p345 p406 p581 p820 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6478 : p1075)
    (h15200 : p7 ∨ (¬ p17) ∨ p230 ∨ (¬ p303) ∨ (¬ p345) ∨ (¬ p406) ∨ (¬ p581) ∨ (¬ p820) ∨ (¬ p1075)) : (¬ p17) ∨ (¬ p303) ∨ (¬ p345) ∨ (¬ p406) ∨ (¬ p581) ∨ (¬ p820) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p820 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p230) := by
    exact h16165
  have u8 : p1075 := by
    exact h6478
  rcases h15200 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u8)

theorem step19766 (p7 p17 p47 p138 p406 p820 p879 p898 p1287 : Prop)
    (h16152 : (¬ p7))
    (h15201 : p7 ∨ (¬ p17) ∨ (¬ p47) ∨ (¬ p138) ∨ (¬ p406) ∨ (¬ p820) ∨ (¬ p879) ∨ (¬ p898) ∨ (¬ p1287)) : (¬ p17) ∨ (¬ p47) ∨ (¬ p138) ∨ (¬ p406) ∨ (¬ p820) ∨ (¬ p879) ∨ (¬ p898) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p820 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p879 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p898 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15201 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19767 (p5 p7 p499 p533 p633 p756 p1159 p1465 : Prop)
    (h16152 : (¬ p7))
    (h15202 : (¬ p5) ∨ p7 ∨ (¬ p499) ∨ (¬ p533) ∨ (¬ p633) ∨ (¬ p756) ∨ (¬ p1159) ∨ (¬ p1465)) : (¬ p5) ∨ (¬ p499) ∨ (¬ p533) ∨ (¬ p633) ∨ (¬ p756) ∨ (¬ p1159) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15202 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19768 (p7 p343 p344 p726 p1096 p1136 p1562 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16259 : (¬ p1136))
    (h15203 : p7 ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p726) ∨ (¬ p1096) ∨ p1136 ∨ (¬ p1562)) : (¬ p344) ∨ (¬ p726) ∨ (¬ p1096) ∨ (¬ p1562) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p343 := by
    exact h1950
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h15203 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step19769 (p7 p662 p726 p733 p842 p1022 p1077 : Prop)
    (h16152 : (¬ p7))
    (h15204 : p7 ∨ (¬ p662) ∨ (¬ p726) ∨ (¬ p733) ∨ (¬ p842) ∨ (¬ p1022) ∨ (¬ p1077)) : (¬ p662) ∨ (¬ p726) ∨ (¬ p733) ∨ (¬ p842) ∨ (¬ p1022) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p662 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p733 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p842 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15204 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19770 (p7 p69 p310 p343 p344 p496 p536 p726 p1141 p1324 p1465 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16309 : (¬ p1324))
    (h15205 : p7 ∨ (¬ p69) ∨ (¬ p310) ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p496) ∨ (¬ p536) ∨ (¬ p726) ∨ (¬ p1141) ∨ p1324 ∨ (¬ p1465)) : (¬ p69) ∨ (¬ p310) ∨ (¬ p344) ∨ (¬ p496) ∨ (¬ p536) ∨ (¬ p726) ∨ (¬ p1141) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p343 := by
    exact h1950
  have u10 : (¬ p1324) := by
    exact h16309
  rcases h15205 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (u10 q9)
  · exact False.elim (q10 u7)

theorem step19771 (p7 p123 p287 p303 p406 p427 p537 p680 p769 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h2334 : p427)
    (h15206 : p7 ∨ p123 ∨ (¬ p287) ∨ (¬ p303) ∨ (¬ p406) ∨ (¬ p427) ∨ (¬ p537) ∨ (¬ p680) ∨ (¬ p769)) : (¬ p287) ∨ (¬ p303) ∨ (¬ p406) ∨ (¬ p537) ∨ (¬ p680) ∨ (¬ p769) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p123) := by
    exact h16186
  have u8 : p427 := by
    exact h2334
  rcases h15206 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step19772 (p7 p64 p124 p344 p423 p496 p545 p1159 p1187 : Prop)
    (h16152 : (¬ p7))
    (h15207 : p7 ∨ (¬ p64) ∨ (¬ p124) ∨ (¬ p344) ∨ (¬ p423) ∨ (¬ p496) ∨ (¬ p545) ∨ (¬ p1159) ∨ (¬ p1187)) : (¬ p64) ∨ (¬ p124) ∨ (¬ p344) ∨ (¬ p423) ∨ (¬ p496) ∨ (¬ p545) ∨ (¬ p1159) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15207 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19773 (p7 p20 p123 p126 p188 p279 p420 p423 p1159 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h1444 : p279)
    (h15208 : p7 ∨ (¬ p20) ∨ p123 ∨ (¬ p126) ∨ (¬ p188) ∨ (¬ p279) ∨ (¬ p420) ∨ (¬ p423) ∨ (¬ p1159)) : (¬ p20) ∨ (¬ p126) ∨ (¬ p188) ∨ (¬ p420) ∨ (¬ p423) ∨ (¬ p1159) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p20 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p123) := by
    exact h16186
  have u8 : p279 := by
    exact h1444
  rcases h15208 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step19775 (p7 p85 p125 p227 p601 p918 p1081 p1115 p1160 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16265 : (¬ p1160))
    (h7053 : p1184)
    (h15210 : p7 ∨ (¬ p85) ∨ (¬ p125) ∨ (¬ p227) ∨ (¬ p601) ∨ (¬ p918) ∨ (¬ p1081) ∨ (¬ p1115) ∨ p1160 ∨ (¬ p1184)) : (¬ p85) ∨ (¬ p125) ∨ (¬ p227) ∨ (¬ p601) ∨ (¬ p918) ∨ (¬ p1081) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p1160) := by
    exact h16265
  have u9 : p1184 := by
    exact h7053
  rcases h15210 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (u8 q8)
  · exact False.elim (q9 u9)

theorem step19776 (p7 p18 p209 p423 p961 p1211 : Prop)
    (h16152 : (¬ p7))
    (h15212 : p7 ∨ (¬ p18) ∨ (¬ p209) ∨ (¬ p423) ∨ (¬ p961) ∨ (¬ p1211)) : (¬ p18) ∨ (¬ p209) ∨ (¬ p423) ∨ (¬ p961) ∨ (¬ p1211) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15212 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19777 (p7 p134 p189 p279 p532 p1206 p1324 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16309 : (¬ p1324))
    (h15213 : p7 ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p279) ∨ (¬ p532) ∨ (¬ p1206) ∨ p1324) : (¬ p134) ∨ (¬ p189) ∨ (¬ p532) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p279 := by
    exact h1444
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h15213 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step19778 (p7 p47 p87 p189 p225 p229 p668 p928 p1116 : Prop)
    (h16152 : (¬ p7))
    (h15214 : p7 ∨ (¬ p47) ∨ (¬ p87) ∨ (¬ p189) ∨ (¬ p225) ∨ (¬ p229) ∨ (¬ p668) ∨ (¬ p928) ∨ (¬ p1116)) : (¬ p47) ∨ (¬ p87) ∨ (¬ p189) ∨ (¬ p225) ∨ (¬ p229) ∨ (¬ p668) ∨ (¬ p928) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15214 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19779 (p7 p264 p576 p961 p1273 p1495 : Prop)
    (h16152 : (¬ p7))
    (h15215 : p7 ∨ (¬ p264) ∨ (¬ p576) ∨ (¬ p961) ∨ (¬ p1273) ∨ (¬ p1495)) : (¬ p264) ∨ (¬ p576) ∨ (¬ p961) ∨ (¬ p1273) ∨ (¬ p1495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p264 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15215 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19780 (p7 p8 p87 p101 p121 p158 p261 p657 p686 p928 p961 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h6744 : p1135)
    (h15216 : p7 ∨ (¬ p8) ∨ (¬ p87) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p158) ∨ (¬ p261) ∨ (¬ p657) ∨ p686 ∨ (¬ p928) ∨ (¬ p961) ∨ (¬ p1135)) : (¬ p8) ∨ (¬ p87) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p158) ∨ (¬ p261) ∨ (¬ p657) ∨ (¬ p928) ∨ (¬ p961) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p686) := by
    exact h16205
  have u11 : p1135 := by
    exact h6744
  rcases h15216 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
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
  · exact False.elim (q10 u8)
  · exact False.elim (q11 u11)

theorem step19781 (p7 p12 p225 p304 p426 p681 p1076 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h3892 : p681)
    (h15217 : p7 ∨ (¬ p12) ∨ (¬ p225) ∨ (¬ p304) ∨ p426 ∨ (¬ p681) ∨ (¬ p1076)) : (¬ p12) ∨ (¬ p225) ∨ (¬ p304) ∨ (¬ p1076) := by
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
  have u2 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p426) := by
    exact h16178
  have u6 : p681 := by
    exact h3892
  rcases h15217 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step19782 (p7 p11 p17 p101 p121 p279 p686 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16205 : (¬ p686))
    (h15218 : p7 ∨ (¬ p11) ∨ (¬ p17) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p279) ∨ p686) : (¬ p11) ∨ (¬ p17) ∨ (¬ p101) ∨ (¬ p121) := by
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
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p279 := by
    exact h1444
  have u6 : (¬ p686) := by
    exact h16205
  rcases h15218 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)

theorem step19783 (p7 p206 p283 p344 p659 p686 p836 p961 p1443 : Prop)
    (h16152 : (¬ p7))
    (h3753 : p659)
    (h16205 : (¬ p686))
    (h15219 : p7 ∨ (¬ p206) ∨ (¬ p283) ∨ (¬ p344) ∨ (¬ p659) ∨ p686 ∨ (¬ p836) ∨ (¬ p961) ∨ (¬ p1443)) : (¬ p206) ∨ (¬ p283) ∨ (¬ p344) ∨ (¬ p836) ∨ (¬ p961) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p836 := by
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
  have u7 : p659 := by
    exact h3753
  have u8 : (¬ p686) := by
    exact h16205
  rcases h15219 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u7)
  · exact False.elim (u8 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step19784 (p7 p189 p279 p349 p387 p419 p686 p796 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16205 : (¬ p686))
    (h15220 : p7 ∨ (¬ p189) ∨ (¬ p279) ∨ (¬ p349) ∨ (¬ p387) ∨ (¬ p419) ∨ p686 ∨ (¬ p796)) : (¬ p189) ∨ (¬ p349) ∨ (¬ p387) ∨ (¬ p419) ∨ (¬ p796) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p279 := by
    exact h1444
  have u7 : (¬ p686) := by
    exact h16205
  rcases h15220 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step19785 (p2 p7 p88 p188 p387 p419 p595 p599 p924 p1099 : Prop)
    (h16152 : (¬ p7))
    (h15221 : (¬ p2) ∨ p7 ∨ (¬ p88) ∨ (¬ p188) ∨ (¬ p387) ∨ (¬ p419) ∨ (¬ p595) ∨ (¬ p599) ∨ (¬ p924) ∨ (¬ p1099)) : (¬ p2) ∨ (¬ p88) ∨ (¬ p188) ∨ (¬ p387) ∨ (¬ p419) ∨ (¬ p595) ∨ (¬ p599) ∨ (¬ p924) ∨ (¬ p1099) := by
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
  have u2 : p188 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p599 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15221 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19786 (p7 p226 p328 p348 p481 p664 p1036 : Prop)
    (h16152 : (¬ p7))
    (h15222 : p7 ∨ (¬ p226) ∨ (¬ p328) ∨ (¬ p348) ∨ (¬ p481) ∨ (¬ p664) ∨ (¬ p1036)) : (¬ p226) ∨ (¬ p328) ∨ (¬ p348) ∨ (¬ p481) ∨ (¬ p664) ∨ (¬ p1036) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p328 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15222 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19787 (p7 p189 p279 p419 p796 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16309 : (¬ p1324))
    (h15223 : p7 ∨ (¬ p189) ∨ (¬ p279) ∨ (¬ p419) ∨ (¬ p796) ∨ p1324 ∨ (¬ p1325)) : (¬ p189) ∨ (¬ p419) ∨ (¬ p796) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p279 := by
    exact h1444
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h15223 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step19788 (p7 p189 p279 p302 p796 p997 p1333 p1465 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16285 : (¬ p302))
    (h15224 : p7 ∨ (¬ p189) ∨ (¬ p279) ∨ p302 ∨ (¬ p796) ∨ (¬ p997) ∨ (¬ p1333) ∨ (¬ p1465)) : (¬ p189) ∨ (¬ p796) ∨ (¬ p997) ∨ (¬ p1333) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p997 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p279 := by
    exact h1444
  have u7 : (¬ p302) := by
    exact h16285
  rcases h15224 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (u7 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step19789 (p7 p16 p189 p343 p344 p422 p499 p633 p1324 p1465 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16309 : (¬ p1324))
    (h15225 : p7 ∨ (¬ p16) ∨ (¬ p189) ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p422) ∨ (¬ p499) ∨ (¬ p633) ∨ p1324 ∨ (¬ p1465)) : (¬ p16) ∨ (¬ p189) ∨ (¬ p344) ∨ (¬ p422) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p343 := by
    exact h1950
  have u9 : (¬ p1324) := by
    exact h16309
  rcases h15225 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19790 (p7 p16 p347 p499 p601 p657 p814 p858 : Prop)
    (h16152 : (¬ p7))
    (h15226 : p7 ∨ (¬ p16) ∨ (¬ p347) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p657) ∨ (¬ p814) ∨ (¬ p858)) : (¬ p16) ∨ (¬ p347) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p657) ∨ (¬ p814) ∨ (¬ p858) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15226 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19791 (p7 p134 p163 p257 p346 p544 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h6478 : p1075)
    (h15227 : p7 ∨ (¬ p134) ∨ (¬ p163) ∨ p257 ∨ (¬ p346) ∨ (¬ p544) ∨ (¬ p1075)) : (¬ p134) ∨ (¬ p163) ∨ (¬ p346) ∨ (¬ p544) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p163 := by
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
  rcases h15227 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19792 (p7 p88 p188 p224 p225 p226 p495 p577 p1229 p1291 : Prop)
    (h16152 : (¬ p7))
    (h15228 : p7 ∨ (¬ p88) ∨ (¬ p188) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1229) ∨ (¬ p1291)) : (¬ p88) ∨ (¬ p188) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1229) ∨ (¬ p1291) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p188 := by
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
  have u5 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1291 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15228 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19793 (p7 p134 p257 p406 p424 p476 p1287 p1664 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h10244 : p1664)
    (h15229 : p7 ∨ (¬ p134) ∨ p257 ∨ (¬ p406) ∨ (¬ p424) ∨ (¬ p476) ∨ (¬ p1287) ∨ (¬ p1664)) : (¬ p134) ∨ (¬ p406) ∨ (¬ p424) ∨ (¬ p476) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p476 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p257) := by
    exact h16170
  have u7 : p1664 := by
    exact h10244
  rcases h15229 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step19794 (p7 p16 p185 p595 p980 p1115 p1330 p1542 : Prop)
    (h16152 : (¬ p7))
    (h15230 : p7 ∨ (¬ p16) ∨ (¬ p185) ∨ (¬ p595) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p1330) ∨ (¬ p1542)) : (¬ p16) ∨ (¬ p185) ∨ (¬ p595) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p1330) ∨ (¬ p1542) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
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
  have u4 : p1115 := by
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
  rcases h15230 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19795 (p7 p136 p163 p226 p257 p301 p323 p659 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h3753 : p659)
    (h15231 : p7 ∨ (¬ p136) ∨ (¬ p163) ∨ (¬ p226) ∨ p257 ∨ (¬ p301) ∨ (¬ p323) ∨ (¬ p659)) : (¬ p136) ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p301) ∨ (¬ p323) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p136 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p257) := by
    exact h16170
  have u7 : p659 := by
    exact h3753
  rcases h15231 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step19796 (p7 p11 p124 p125 p126 p1075 p1445 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16350 : (¬ p1445))
    (h15232 : p7 ∨ (¬ p11) ∨ (¬ p124) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p1075) ∨ p1445) : (¬ p11) ∨ (¬ p124) ∨ (¬ p125) ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
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
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p1075 := by
    exact h6478
  have u6 : (¬ p1445) := by
    exact h16350
  rcases h15232 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)

theorem step19797 (p7 p167 p882 p1041 p1074 p1256 : Prop)
    (h16152 : (¬ p7))
    (h15233 : p7 ∨ (¬ p167) ∨ (¬ p882) ∨ (¬ p1041) ∨ (¬ p1074) ∨ (¬ p1256)) : (¬ p167) ∨ (¬ p882) ∨ (¬ p1041) ∨ (¬ p1074) ∨ (¬ p1256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p167 := by
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
  have u4 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15233 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19798 (p7 p122 p134 p257 p328 p420 p424 p455 : Prop)
    (h16152 : (¬ p7))
    (h10260 : p122)
    (h16170 : (¬ p257))
    (h15234 : p7 ∨ (¬ p122) ∨ (¬ p134) ∨ p257 ∨ (¬ p328) ∨ (¬ p420) ∨ (¬ p424) ∨ (¬ p455)) : (¬ p134) ∨ (¬ p328) ∨ (¬ p420) ∨ (¬ p424) ∨ (¬ p455) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p328 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p122 := by
    exact h10260
  have u7 : (¬ p257) := by
    exact h16170
  rcases h15234 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (u7 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step19799 (p5 p7 p110 p167 p499 p633 p1159 p1256 : Prop)
    (h16152 : (¬ p7))
    (h15235 : (¬ p5) ∨ p7 ∨ (¬ p110) ∨ (¬ p167) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p1159) ∨ (¬ p1256)) : (¬ p5) ∨ (¬ p110) ∨ (¬ p167) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p1159) ∨ (¬ p1256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15235 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19800 (p7 p88 p189 p422 p595 p924 p1099 p1135 p1286 p1324 p1465 : Prop)
    (h16152 : (¬ p7))
    (h6744 : p1135)
    (h16309 : (¬ p1324))
    (h15237 : p7 ∨ (¬ p88) ∨ (¬ p189) ∨ (¬ p422) ∨ (¬ p595) ∨ (¬ p924) ∨ (¬ p1099) ∨ (¬ p1135) ∨ (¬ p1286) ∨ p1324 ∨ (¬ p1465)) : (¬ p88) ∨ (¬ p189) ∨ (¬ p422) ∨ (¬ p595) ∨ (¬ p924) ∨ (¬ p1099) ∨ (¬ p1286) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p1135 := by
    exact h6744
  have u10 : (¬ p1324) := by
    exact h16309
  rcases h15237 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u6)
  · exact False.elim (u10 q9)
  · exact False.elim (q10 u7)

theorem step19801 (p7 p431 p666 p710 p734 p1061 : Prop)
    (h16152 : (¬ p7))
    (h15238 : p7 ∨ (¬ p431) ∨ (¬ p666) ∨ (¬ p710) ∨ (¬ p734) ∨ (¬ p1061)) : (¬ p431) ∨ (¬ p666) ∨ (¬ p710) ∨ (¬ p734) ∨ (¬ p1061) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15238 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19802 (p7 p344 p638 p728 p898 p1545 : Prop)
    (h16152 : (¬ p7))
    (h15239 : p7 ∨ (¬ p344) ∨ (¬ p638) ∨ (¬ p728) ∨ (¬ p898) ∨ (¬ p1545)) : (¬ p344) ∨ (¬ p638) ∨ (¬ p728) ∨ (¬ p898) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p638 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p898 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15239 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19803 (p7 p16 p189 p422 p595 p1330 p1465 p1542 : Prop)
    (h16152 : (¬ p7))
    (h15240 : p7 ∨ (¬ p16) ∨ (¬ p189) ∨ (¬ p422) ∨ (¬ p595) ∨ (¬ p1330) ∨ (¬ p1465) ∨ (¬ p1542)) : (¬ p16) ∨ (¬ p189) ∨ (¬ p422) ∨ (¬ p595) ∨ (¬ p1330) ∨ (¬ p1465) ∨ (¬ p1542) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15240 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19804 (p7 p88 p189 p422 p657 p734 p903 p924 p1135 p1324 p1465 p1542 : Prop)
    (h16152 : (¬ p7))
    (h6744 : p1135)
    (h16309 : (¬ p1324))
    (h15241 : p7 ∨ (¬ p88) ∨ (¬ p189) ∨ (¬ p422) ∨ (¬ p657) ∨ (¬ p734) ∨ (¬ p903) ∨ (¬ p924) ∨ (¬ p1135) ∨ p1324 ∨ (¬ p1465) ∨ (¬ p1542)) : (¬ p88) ∨ (¬ p189) ∨ (¬ p422) ∨ (¬ p657) ∨ (¬ p734) ∨ (¬ p903) ∨ (¬ p924) ∨ (¬ p1465) ∨ (¬ p1542) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p903 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p1135 := by
    exact h6744
  have u11 : (¬ p1324) := by
    exact h16309
  rcases h15241 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u10)
  · exact False.elim (u11 q9)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step19805 (p7 p8 p88 p189 p422 p728 p924 p1098 p1330 p1465 : Prop)
    (h16152 : (¬ p7))
    (h15242 : p7 ∨ (¬ p8) ∨ (¬ p88) ∨ (¬ p189) ∨ (¬ p422) ∨ (¬ p728) ∨ (¬ p924) ∨ (¬ p1098) ∨ (¬ p1330) ∨ (¬ p1465)) : (¬ p8) ∨ (¬ p88) ∨ (¬ p189) ∨ (¬ p422) ∨ (¬ p728) ∨ (¬ p924) ∨ (¬ p1098) ∨ (¬ p1330) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1098 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15242 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19806 (p7 p8 p63 p431 p616 p657 p924 p1098 p1545 : Prop)
    (h16152 : (¬ p7))
    (h15243 : p7 ∨ (¬ p8) ∨ (¬ p63) ∨ (¬ p431) ∨ (¬ p616) ∨ (¬ p657) ∨ (¬ p924) ∨ (¬ p1098) ∨ (¬ p1545)) : (¬ p8) ∨ (¬ p63) ∨ (¬ p431) ∨ (¬ p616) ∨ (¬ p657) ∨ (¬ p924) ∨ (¬ p1098) ∨ (¬ p1545) := by
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
  have u2 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1098 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15243 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19808 (p7 p16 p167 p189 p225 p347 p499 p601 : Prop)
    (h16152 : (¬ p7))
    (h15245 : p7 ∨ (¬ p16) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p225) ∨ (¬ p347) ∨ (¬ p499) ∨ (¬ p601)) : (¬ p16) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p225) ∨ (¬ p347) ∨ (¬ p499) ∨ (¬ p601) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15245 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19809 (p7 p88 p134 p188 p257 p303 p406 p427 p495 p577 p620 p1159 p1256 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h2334 : p427)
    (h15246 : p7 ∨ (¬ p88) ∨ (¬ p134) ∨ (¬ p188) ∨ p257 ∨ (¬ p303) ∨ (¬ p406) ∨ (¬ p427) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p620) ∨ (¬ p1159) ∨ (¬ p1256)) : (¬ p88) ∨ (¬ p134) ∨ (¬ p188) ∨ (¬ p303) ∨ (¬ p406) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p620) ∨ (¬ p1159) ∨ (¬ p1256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p620 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : (¬ p257) := by
    exact h16170
  have u12 : p427 := by
    exact h2334
  rcases h15246 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u11 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u12)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)
  · exact False.elim (q12 u9)

theorem step19810 (p7 p38 p43 p495 p577 p1159 p1229 p1291 p1333 p1465 : Prop)
    (h16152 : (¬ p7))
    (h15247 : p7 ∨ (¬ p38) ∨ (¬ p43) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1159) ∨ (¬ p1229) ∨ (¬ p1291) ∨ (¬ p1333) ∨ (¬ p1465)) : (¬ p38) ∨ (¬ p43) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1159) ∨ (¬ p1229) ∨ (¬ p1291) ∨ (¬ p1333) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1291 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15247 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19811 (p7 p189 p279 p302 p422 p1333 p1465 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16285 : (¬ p302))
    (h15248 : p7 ∨ (¬ p189) ∨ (¬ p279) ∨ p302 ∨ (¬ p422) ∨ (¬ p1333) ∨ (¬ p1465)) : (¬ p189) ∨ (¬ p422) ∨ (¬ p1333) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p279 := by
    exact h1444
  have u6 : (¬ p302) := by
    exact h16285
  rcases h15248 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19812 (p2 p7 p88 p110 p167 p188 p424 p726 p924 p1562 : Prop)
    (h16152 : (¬ p7))
    (h15249 : (¬ p2) ∨ p7 ∨ (¬ p88) ∨ (¬ p110) ∨ (¬ p167) ∨ (¬ p188) ∨ (¬ p424) ∨ (¬ p726) ∨ (¬ p924) ∨ (¬ p1562)) : (¬ p2) ∨ (¬ p88) ∨ (¬ p110) ∨ (¬ p167) ∨ (¬ p188) ∨ (¬ p424) ∨ (¬ p726) ∨ (¬ p924) ∨ (¬ p1562) := by
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
  have u2 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15249 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19813 (p7 p88 p189 p419 p495 p577 p796 p1229 p1291 : Prop)
    (h16152 : (¬ p7))
    (h15250 : p7 ∨ (¬ p88) ∨ (¬ p189) ∨ (¬ p419) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p796) ∨ (¬ p1229) ∨ (¬ p1291)) : (¬ p88) ∨ (¬ p189) ∨ (¬ p419) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p796) ∨ (¬ p1229) ∨ (¬ p1291) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1291 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15250 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19814 (p7 p44 p63 p69 p422 p792 p1324 p1465 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16309 : (¬ p1324))
    (h15251 : p7 ∨ (¬ p44) ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p422) ∨ (¬ p792) ∨ p1324 ∨ (¬ p1465)) : (¬ p44) ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p422) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p792 := by
    exact h4535
  have u7 : (¬ p1324) := by
    exact h16309
  rcases h15251 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step19815 (p7 p63 p64 p134 p257 p792 p1159 p1256 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h4535 : p792)
    (h15252 : p7 ∨ (¬ p63) ∨ (¬ p64) ∨ (¬ p134) ∨ p257 ∨ (¬ p792) ∨ (¬ p1159) ∨ (¬ p1256)) : (¬ p63) ∨ (¬ p64) ∨ (¬ p134) ∨ (¬ p1159) ∨ (¬ p1256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p257) := by
    exact h16170
  have u7 : p792 := by
    exact h4535
  rcases h15252 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step19816 (p7 p185 p193 p406 p799 p816 p985 p1333 p1584 : Prop)
    (h16152 : (¬ p7))
    (h15254 : p7 ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p406) ∨ (¬ p799) ∨ (¬ p816) ∨ (¬ p985) ∨ (¬ p1333) ∨ (¬ p1584)) : (¬ p185) ∨ (¬ p193) ∨ (¬ p406) ∨ (¬ p799) ∨ (¬ p816) ∨ (¬ p985) ∨ (¬ p1333) ∨ (¬ p1584) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p799 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p816 := by
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
  have u7 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15254 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19817 (p7 p125 p264 p518 p576 p1393 : Prop)
    (h16152 : (¬ p7))
    (h15255 : p7 ∨ (¬ p125) ∨ (¬ p264) ∨ (¬ p518) ∨ (¬ p576) ∨ (¬ p1393)) : (¬ p125) ∨ (¬ p264) ∨ (¬ p518) ∨ (¬ p576) ∨ (¬ p1393) := by
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
  have u2 : p518 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15255 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19818 (p7 p107 p304 p348 p362 p664 p1036 : Prop)
    (h16152 : (¬ p7))
    (h15256 : p7 ∨ (¬ p107) ∨ (¬ p304) ∨ (¬ p348) ∨ (¬ p362) ∨ (¬ p664) ∨ (¬ p1036)) : (¬ p107) ∨ (¬ p304) ∨ (¬ p348) ∨ (¬ p362) ∨ (¬ p664) ∨ (¬ p1036) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15256 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19819 (p257 p1035 p1213 p1386 : Prop)
    (h16170 : (¬ p257))
    (h8348 : p1386)
    (h15257 : p257 ∨ (¬ p1035) ∨ p1213 ∨ (¬ p1386)) : (¬ p1035) ∨ p1213 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1213) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p257) := by
    exact h16170
  have u3 : p1386 := by
    exact h8348
  rcases h15257 with q0 | q1 | q2 | q3
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)

theorem step19820 (p7 p41 p83 p189 p918 p1115 p1181 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16272 : (¬ p1181))
    (h7053 : p1184)
    (h15258 : p7 ∨ (¬ p41) ∨ (¬ p83) ∨ (¬ p189) ∨ (¬ p918) ∨ (¬ p1115) ∨ p1181 ∨ (¬ p1184)) : (¬ p41) ∨ (¬ p83) ∨ (¬ p189) ∨ (¬ p918) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p83 := by
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
  have u4 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p1181) := by
    exact h16272
  have u7 : p1184 := by
    exact h7053
  rcases h15258 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u7)

theorem step19821 (p7 p209 p532 p961 p1035 p1212 : Prop)
    (h16152 : (¬ p7))
    (h15259 : p7 ∨ (¬ p209) ∨ (¬ p532) ∨ (¬ p961) ∨ (¬ p1035) ∨ (¬ p1212)) : (¬ p209) ∨ (¬ p532) ∨ (¬ p961) ∨ (¬ p1035) ∨ (¬ p1212) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1212 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15259 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19822 (p7 p18 p47 p87 p101 p189 p262 p350 p362 p581 : Prop)
    (h16152 : (¬ p7))
    (h15260 : p7 ∨ (¬ p18) ∨ (¬ p47) ∨ (¬ p87) ∨ (¬ p101) ∨ (¬ p189) ∨ (¬ p262) ∨ (¬ p350) ∨ (¬ p362) ∨ (¬ p581)) : (¬ p18) ∨ (¬ p47) ∨ (¬ p87) ∨ (¬ p101) ∨ (¬ p189) ∨ (¬ p262) ∨ (¬ p350) ∨ (¬ p362) ∨ (¬ p581) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15260 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19823 (p7 p12 p108 p209 p304 p1076 : Prop)
    (h16152 : (¬ p7))
    (h15261 : p7 ∨ (¬ p12) ∨ (¬ p108) ∨ (¬ p209) ∨ (¬ p304) ∨ (¬ p1076)) : (¬ p12) ∨ (¬ p108) ∨ (¬ p209) ∨ (¬ p304) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15261 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19824 (p7 p47 p87 p158 p189 p435 p536 p735 p928 p1187 : Prop)
    (h16152 : (¬ p7))
    (h15262 : p7 ∨ (¬ p47) ∨ (¬ p87) ∨ (¬ p158) ∨ (¬ p189) ∨ (¬ p435) ∨ (¬ p536) ∨ (¬ p735) ∨ (¬ p928) ∨ (¬ p1187)) : (¬ p47) ∨ (¬ p87) ∨ (¬ p158) ∨ (¬ p189) ∨ (¬ p435) ∨ (¬ p536) ∨ (¬ p735) ∨ (¬ p928) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p735 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15262 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19826 (p7 p41 p83 p124 p189 p344 p496 p842 p1385 : Prop)
    (h16152 : (¬ p7))
    (h15264 : p7 ∨ (¬ p41) ∨ (¬ p83) ∨ (¬ p124) ∨ (¬ p189) ∨ (¬ p344) ∨ (¬ p496) ∨ (¬ p842) ∨ (¬ p1385)) : (¬ p41) ∨ (¬ p83) ∨ (¬ p124) ∨ (¬ p189) ∨ (¬ p344) ∨ (¬ p496) ∨ (¬ p842) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p496 := by
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
  rcases h15264 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19827 (p7 p87 p167 p189 p406 p669 p816 p1036 p1393 : Prop)
    (h16152 : (¬ p7))
    (h15265 : p7 ∨ (¬ p87) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p406) ∨ (¬ p669) ∨ (¬ p816) ∨ (¬ p1036) ∨ (¬ p1393)) : (¬ p87) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p406) ∨ (¬ p669) ∨ (¬ p816) ∨ (¬ p1036) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15265 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19828 (p7 p10 p41 p83 p137 p189 p280 p576 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16173 : (¬ p280))
    (h7053 : p1184)
    (h15266 : p7 ∨ (¬ p10) ∨ (¬ p41) ∨ (¬ p83) ∨ (¬ p137) ∨ (¬ p189) ∨ p280 ∨ (¬ p576) ∨ (¬ p1184)) : (¬ p10) ∨ (¬ p41) ∨ (¬ p83) ∨ (¬ p137) ∨ (¬ p189) ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p137 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p280) := by
    exact h16173
  have u8 : p1184 := by
    exact h7053
  rcases h15266 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u8)

theorem step19829 (p7 p41 p83 p189 p257 p323 p515 p1184 p1385 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h7053 : p1184)
    (h15267 : p7 ∨ (¬ p41) ∨ (¬ p83) ∨ (¬ p189) ∨ p257 ∨ (¬ p323) ∨ (¬ p515) ∨ (¬ p1184) ∨ (¬ p1385)) : (¬ p41) ∨ (¬ p83) ∨ (¬ p189) ∨ (¬ p323) ∨ (¬ p515) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p515 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p257) := by
    exact h16170
  have u8 : p1184 := by
    exact h7053
  rcases h15267 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u5)

theorem step19830 (p7 p41 p83 p166 p189 p225 p426 p918 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h7053 : p1184)
    (h15268 : p7 ∨ (¬ p41) ∨ (¬ p83) ∨ (¬ p166) ∨ (¬ p189) ∨ (¬ p225) ∨ p426 ∨ (¬ p918) ∨ (¬ p1184)) : (¬ p41) ∨ (¬ p83) ∨ (¬ p166) ∨ (¬ p189) ∨ (¬ p225) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p166 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p426) := by
    exact h16178
  have u8 : p1184 := by
    exact h7053
  rcases h15268 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u8)

theorem step19832 (p7 p83 p160 p167 p189 p669 p1036 p1233 p1325 : Prop)
    (h16152 : (¬ p7))
    (h15270 : p7 ∨ (¬ p83) ∨ (¬ p160) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p669) ∨ (¬ p1036) ∨ (¬ p1233) ∨ (¬ p1325)) : (¬ p83) ∨ (¬ p160) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p669) ∨ (¬ p1036) ∨ (¬ p1233) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1233 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15270 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19833 (p7 p125 p227 p257 p323 p383 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h8348 : p1386)
    (h15271 : p7 ∨ (¬ p125) ∨ (¬ p227) ∨ p257 ∨ (¬ p323) ∨ (¬ p383) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p125) ∨ (¬ p227) ∨ (¬ p323) ∨ (¬ p383) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p383 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p257) := by
    exact h16170
  have u7 : p1386 := by
    exact h8348
  rcases h15271 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step19834 (p7 p47 p87 p124 p189 p262 p344 p545 p581 p1187 : Prop)
    (h16152 : (¬ p7))
    (h15272 : p7 ∨ (¬ p47) ∨ (¬ p87) ∨ (¬ p124) ∨ (¬ p189) ∨ (¬ p262) ∨ (¬ p344) ∨ (¬ p545) ∨ (¬ p581) ∨ (¬ p1187)) : (¬ p47) ∨ (¬ p87) ∨ (¬ p124) ∨ (¬ p189) ∨ (¬ p262) ∨ (¬ p344) ∨ (¬ p545) ∨ (¬ p581) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15272 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19835 (p7 p47 p87 p189 p229 p406 p669 p816 p1036 p1393 : Prop)
    (h16152 : (¬ p7))
    (h15274 : p7 ∨ (¬ p47) ∨ (¬ p87) ∨ (¬ p189) ∨ (¬ p229) ∨ (¬ p406) ∨ (¬ p669) ∨ (¬ p816) ∨ (¬ p1036) ∨ (¬ p1393)) : (¬ p47) ∨ (¬ p87) ∨ (¬ p189) ∨ (¬ p229) ∨ (¬ p406) ∨ (¬ p669) ∨ (¬ p816) ∨ (¬ p1036) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15274 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19836 (p7 p8 p87 p158 p189 p422 p657 p928 p1004 : Prop)
    (h16152 : (¬ p7))
    (h15275 : p7 ∨ (¬ p8) ∨ (¬ p87) ∨ (¬ p158) ∨ (¬ p189) ∨ (¬ p422) ∨ (¬ p657) ∨ (¬ p928) ∨ (¬ p1004)) : (¬ p8) ∨ (¬ p87) ∨ (¬ p158) ∨ (¬ p189) ∨ (¬ p422) ∨ (¬ p657) ∨ (¬ p928) ∨ (¬ p1004) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15275 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19837 (p7 p41 p83 p189 p224 p406 p680 p842 p1100 p1385 : Prop)
    (h16152 : (¬ p7))
    (h15276 : p7 ∨ (¬ p41) ∨ (¬ p83) ∨ (¬ p189) ∨ (¬ p224) ∨ (¬ p406) ∨ (¬ p680) ∨ (¬ p842) ∨ (¬ p1100) ∨ (¬ p1385)) : (¬ p41) ∨ (¬ p83) ∨ (¬ p189) ∨ (¬ p224) ∨ (¬ p406) ∨ (¬ p680) ∨ (¬ p842) ∨ (¬ p1100) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p842 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1100 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15276 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19838 (p7 p8 p41 p83 p102 p189 p257 p306 p657 p1004 p1184 p1249 p1253 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h7053 : p1184)
    (h15277 : p7 ∨ (¬ p8) ∨ (¬ p41) ∨ (¬ p83) ∨ (¬ p102) ∨ (¬ p189) ∨ p257 ∨ (¬ p306) ∨ (¬ p657) ∨ (¬ p1004) ∨ (¬ p1184) ∨ (¬ p1249) ∨ (¬ p1253)) : (¬ p8) ∨ (¬ p41) ∨ (¬ p83) ∨ (¬ p102) ∨ (¬ p189) ∨ (¬ p306) ∨ (¬ p657) ∨ (¬ p1004) ∨ (¬ p1249) ∨ (¬ p1253) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1253 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : (¬ p257) := by
    exact h16170
  have u12 : p1184 := by
    exact h7053
  rcases h15277 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
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

theorem step19839 (p7 p47 p125 p189 p227 p229 p279 p601 p1036 p1081 p1160 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16265 : (¬ p1160))
    (h15278 : p7 ∨ (¬ p47) ∨ (¬ p125) ∨ (¬ p189) ∨ (¬ p227) ∨ (¬ p229) ∨ (¬ p279) ∨ (¬ p601) ∨ (¬ p1036) ∨ (¬ p1081) ∨ p1160) : (¬ p47) ∨ (¬ p125) ∨ (¬ p189) ∨ (¬ p227) ∨ (¬ p229) ∨ (¬ p601) ∨ (¬ p1036) ∨ (¬ p1081) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p279 := by
    exact h1444
  have u10 : (¬ p1160) := by
    exact h16265
  rcases h15278 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (u10 q10)

theorem step19840 (p7 p8 p18 p69 p389 p657 p1100 p1206 : Prop)
    (h16152 : (¬ p7))
    (h15279 : p7 ∨ (¬ p8) ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p389) ∨ (¬ p657) ∨ (¬ p1100) ∨ (¬ p1206)) : (¬ p8) ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p389) ∨ (¬ p657) ∨ (¬ p1100) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
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
  have u3 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1100 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15279 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19841 (p7 p18 p69 p160 p389 p1206 p1233 p1325 : Prop)
    (h16152 : (¬ p7))
    (h15280 : p7 ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p160) ∨ (¬ p389) ∨ (¬ p1206) ∨ (¬ p1233) ∨ (¬ p1325)) : (¬ p18) ∨ (¬ p69) ∨ (¬ p160) ∨ (¬ p389) ∨ (¬ p1206) ∨ (¬ p1233) ∨ (¬ p1325) := by
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
  have u2 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1233 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15280 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19842 (p7 p18 p47 p87 p189 p389 p406 p816 p1206 p1393 : Prop)
    (h16152 : (¬ p7))
    (h15281 : p7 ∨ (¬ p18) ∨ (¬ p47) ∨ (¬ p87) ∨ (¬ p189) ∨ (¬ p389) ∨ (¬ p406) ∨ (¬ p816) ∨ (¬ p1206) ∨ (¬ p1393)) : (¬ p18) ∨ (¬ p47) ∨ (¬ p87) ∨ (¬ p189) ∨ (¬ p389) ∨ (¬ p406) ∨ (¬ p816) ∨ (¬ p1206) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15281 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19843 (p7 p17 p83 p344 p581 p686 p835 p1184 p1385 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h7053 : p1184)
    (h15282 : p7 ∨ (¬ p17) ∨ (¬ p83) ∨ (¬ p344) ∨ (¬ p581) ∨ p686 ∨ (¬ p835) ∨ (¬ p1184) ∨ (¬ p1385)) : (¬ p17) ∨ (¬ p83) ∨ (¬ p344) ∨ (¬ p581) ∨ (¬ p835) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p835 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p686) := by
    exact h16205
  have u8 : p1184 := by
    exact h7053
  rcases h15282 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u7 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u5)

theorem step19844 (p7 p240 p769 p918 p1589 p1771 : Prop)
    (h16152 : (¬ p7))
    (h15283 : p7 ∨ (¬ p240) ∨ (¬ p769) ∨ (¬ p918) ∨ (¬ p1589) ∨ (¬ p1771)) : (¬ p240) ∨ (¬ p769) ∨ (¬ p918) ∨ (¬ p1589) ∨ (¬ p1771) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p240 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1589 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1771 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15283 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19845 (p7 p17 p279 p406 p581 p656 p904 p919 p1333 p1516 p1772 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16230 : (¬ p919))
    (h15284 : p7 ∨ (¬ p17) ∨ (¬ p279) ∨ (¬ p406) ∨ (¬ p581) ∨ (¬ p656) ∨ (¬ p904) ∨ p919 ∨ (¬ p1333) ∨ (¬ p1516) ∨ (¬ p1772)) : (¬ p17) ∨ (¬ p406) ∨ (¬ p581) ∨ (¬ p656) ∨ (¬ p904) ∨ (¬ p1333) ∨ (¬ p1516) ∨ (¬ p1772) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p656 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1516 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1772 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p279 := by
    exact h1444
  have u10 : (¬ p919) := by
    exact h16230
  rcases h15284 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19846 (p7 p18 p47 p189 p279 p536 p710 p758 p904 p919 p1666 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16230 : (¬ p919))
    (h15285 : p7 ∨ (¬ p18) ∨ (¬ p47) ∨ (¬ p189) ∨ (¬ p279) ∨ (¬ p536) ∨ (¬ p710) ∨ (¬ p758) ∨ (¬ p904) ∨ p919 ∨ (¬ p1666)) : (¬ p18) ∨ (¬ p47) ∨ (¬ p189) ∨ (¬ p536) ∨ (¬ p710) ∨ (¬ p758) ∨ (¬ p904) ∨ (¬ p1666) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p758 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p279 := by
    exact h1444
  have u10 : (¬ p919) := by
    exact h16230
  rcases h15285 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (u10 q9)
  · exact False.elim (q10 u7)

theorem step19847 (p7 p280 p420 p455 p1135 p1325 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16173 : (¬ p280))
    (h6744 : p1135)
    (h15286 : p7 ∨ p280 ∨ (¬ p420) ∨ (¬ p455) ∨ (¬ p1135) ∨ (¬ p1325) ∨ (¬ p1452)) : (¬ p420) ∨ (¬ p455) ∨ (¬ p1325) ∨ (¬ p1452) := by
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
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p280) := by
    exact h16173
  have u6 : p1135 := by
    exact h6744
  rcases h15286 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19848 (p7 p45 p85 p134 p210 p496 : Prop)
    (h16152 : (¬ p7))
    (h15287 : p7 ∨ (¬ p45) ∨ (¬ p85) ∨ (¬ p134) ∨ (¬ p210) ∨ (¬ p496)) : (¬ p45) ∨ (¬ p85) ∨ (¬ p134) ∨ (¬ p210) ∨ (¬ p496) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15287 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19849 (p7 p45 p124 p193 p521 p601 p636 p658 p792 p862 p1349 : Prop)
    (h16152 : (¬ p7))
    (h16199 : (¬ p658))
    (h4535 : p792)
    (h15289 : p7 ∨ (¬ p45) ∨ (¬ p124) ∨ (¬ p193) ∨ (¬ p521) ∨ (¬ p601) ∨ (¬ p636) ∨ p658 ∨ (¬ p792) ∨ (¬ p862) ∨ (¬ p1349)) : (¬ p45) ∨ (¬ p124) ∨ (¬ p193) ∨ (¬ p521) ∨ (¬ p601) ∨ (¬ p636) ∨ (¬ p862) ∨ (¬ p1349) := by
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
  have u3 : p521 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p862 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p658) := by
    exact h16199
  have u10 : p792 := by
    exact h4535
  rcases h15289 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u9 q7)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step19850 (p7 p370 p384 p406 p456 p601 : Prop)
    (h16152 : (¬ p7))
    (h15290 : p7 ∨ (¬ p370) ∨ (¬ p384) ∨ (¬ p406) ∨ (¬ p456) ∨ (¬ p601)) : (¬ p370) ∨ (¬ p384) ∨ (¬ p406) ∨ (¬ p456) ∨ (¬ p601) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p370 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p384 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15290 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19851 (p7 p16 p189 p435 p796 p1225 p1229 p1335 : Prop)
    (h16152 : (¬ p7))
    (h15291 : p7 ∨ (¬ p16) ∨ (¬ p189) ∨ (¬ p435) ∨ (¬ p796) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1335)) : (¬ p16) ∨ (¬ p189) ∨ (¬ p435) ∨ (¬ p796) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1335) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p796 := by
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
  have u6 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15291 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19852 (p7 p16 p124 p189 p331 p498 p601 p636 p796 : Prop)
    (h16152 : (¬ p7))
    (h15292 : p7 ∨ (¬ p16) ∨ (¬ p124) ∨ (¬ p189) ∨ (¬ p331) ∨ (¬ p498) ∨ (¬ p601) ∨ (¬ p636) ∨ (¬ p796)) : (¬ p16) ∨ (¬ p124) ∨ (¬ p189) ∨ (¬ p331) ∨ (¬ p498) ∨ (¬ p601) ∨ (¬ p636) ∨ (¬ p796) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15292 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19853 (p7 p138 p166 p185 p193 p225 p262 p303 p347 p368 p406 : Prop)
    (h16152 : (¬ p7))
    (h15293 : p7 ∨ (¬ p138) ∨ (¬ p166) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p225) ∨ (¬ p262) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p368) ∨ (¬ p406)) : (¬ p138) ∨ (¬ p166) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p225) ∨ (¬ p262) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p368) ∨ (¬ p406) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p166 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h15293 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19854 (p7 p185 p664 p790 p833 p1115 : Prop)
    (h16152 : (¬ p7))
    (h15294 : p7 ∨ (¬ p185) ∨ (¬ p664) ∨ (¬ p790) ∨ (¬ p833) ∨ (¬ p1115)) : (¬ p185) ∨ (¬ p664) ∨ (¬ p790) ∨ (¬ p833) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p833 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15294 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19855 (p7 p124 p138 p193 p262 p980 p1083 p1124 p1349 p1452 : Prop)
    (h16152 : (¬ p7))
    (h15295 : p7 ∨ (¬ p124) ∨ (¬ p138) ∨ (¬ p193) ∨ (¬ p262) ∨ (¬ p980) ∨ (¬ p1083) ∨ (¬ p1124) ∨ (¬ p1349) ∨ (¬ p1452)) : (¬ p124) ∨ (¬ p138) ∨ (¬ p193) ∨ (¬ p262) ∨ (¬ p980) ∨ (¬ p1083) ∨ (¬ p1124) ∨ (¬ p1349) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1083 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15295 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19856 (p7 p69 p124 p496 p983 p1077 p1473 p1710 : Prop)
    (h16152 : (¬ p7))
    (h15296 : p7 ∨ (¬ p69) ∨ (¬ p124) ∨ (¬ p496) ∨ (¬ p983) ∨ (¬ p1077) ∨ (¬ p1473) ∨ (¬ p1710)) : (¬ p69) ∨ (¬ p124) ∨ (¬ p496) ∨ (¬ p983) ∨ (¬ p1077) ∨ (¬ p1473) ∨ (¬ p1710) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1473 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15296 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19857 (p7 p124 p230 p262 p581 p983 p1077 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h8348 : p1386)
    (h15297 : p7 ∨ (¬ p124) ∨ p230 ∨ (¬ p262) ∨ (¬ p581) ∨ (¬ p983) ∨ (¬ p1077) ∨ (¬ p1386)) : (¬ p124) ∨ (¬ p262) ∨ (¬ p581) ∨ (¬ p983) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p1386 := by
    exact h8348
  rcases h15297 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step19858 (p7 p303 p348 p545 p1002 p1035 p1325 : Prop)
    (h16152 : (¬ p7))
    (h15298 : p7 ∨ (¬ p303) ∨ (¬ p348) ∨ (¬ p545) ∨ (¬ p1002) ∨ (¬ p1035) ∨ (¬ p1325)) : (¬ p303) ∨ (¬ p348) ∨ (¬ p545) ∨ (¬ p1002) ∨ (¬ p1035) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1002 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15298 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19859 (p7 p42 p166 p185 p193 p224 p225 p302 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16285 : (¬ p302))
    (h15299 : p7 ∨ (¬ p42) ∨ (¬ p166) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p224) ∨ (¬ p225) ∨ p302) : (¬ p166) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p224) ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p166 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p302) := by
    exact h16285
  rcases h15299 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step19861 (p7 p44 p69 p134 p330 p595 p1192 : Prop)
    (h16152 : (¬ p7))
    (h15301 : p7 ∨ (¬ p44) ∨ (¬ p69) ∨ (¬ p134) ∨ (¬ p330) ∨ (¬ p595) ∨ (¬ p1192)) : (¬ p44) ∨ (¬ p69) ∨ (¬ p134) ∨ (¬ p330) ∨ (¬ p595) ∨ (¬ p1192) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15301 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19862 (p164 p886 p1096 p1136 : Prop)
    (h789 : p164)
    (h16259 : (¬ p1136))
    (h15303 : (¬ p164) ∨ p886 ∨ (¬ p1096) ∨ p1136) : p886 ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p886) := fun hu => hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p164 := by
    exact h789
  have u3 : (¬ p1136) := by
    exact h16259
  rcases h15303 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u3 q3)

theorem step19863 (p7 p14 p20 p109 p207 p227 p456 : Prop)
    (h16152 : (¬ p7))
    (h15304 : p7 ∨ (¬ p14) ∨ (¬ p20) ∨ (¬ p109) ∨ (¬ p207) ∨ (¬ p227) ∨ (¬ p456)) : (¬ p14) ∨ (¬ p20) ∨ (¬ p109) ∨ (¬ p207) ∨ (¬ p227) ∨ (¬ p456) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
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
  have u3 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15304 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19865 (p7 p125 p142 p191 p206 p323 : Prop)
    (h16152 : (¬ p7))
    (h15306 : p7 ∨ (¬ p125) ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p206) ∨ (¬ p323)) : (¬ p125) ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p206) ∨ (¬ p323) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15306 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19866 (p7 p14 p18 p129 p142 p343 p544 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h1950 : p343)
    (h15307 : p7 ∨ (¬ p14) ∨ (¬ p18) ∨ p129 ∨ (¬ p142) ∨ (¬ p343) ∨ (¬ p544)) : (¬ p14) ∨ (¬ p18) ∨ (¬ p142) ∨ (¬ p544) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p343 := by
    exact h1950
  rcases h15307 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step19867 (p7 p63 p124 p421 p577 p616 p665 p1077 p1287 : Prop)
    (h16152 : (¬ p7))
    (h15308 : p7 ∨ (¬ p63) ∨ (¬ p124) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p616) ∨ (¬ p665) ∨ (¬ p1077) ∨ (¬ p1287)) : (¬ p63) ∨ (¬ p124) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p616) ∨ (¬ p665) ∨ (¬ p1077) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15308 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19868 (p6 p7 p129 p142 p1035 p1140 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h8348 : p1386)
    (h15309 : (¬ p6) ∨ p7 ∨ p129 ∨ (¬ p142) ∨ (¬ p1035) ∨ (¬ p1140) ∨ (¬ p1386)) : (¬ p6) ∨ (¬ p142) ∨ (¬ p1035) ∨ (¬ p1140) := by
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
  have u2 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p1386 := by
    exact h8348
  rcases h15309 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19869 (p7 p11 p13 p85 p129 p576 p980 p1142 p1184 p1225 p1256 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h7053 : p1184)
    (h15310 : p7 ∨ (¬ p11) ∨ (¬ p13) ∨ (¬ p85) ∨ p129 ∨ (¬ p576) ∨ (¬ p980) ∨ (¬ p1142) ∨ (¬ p1184) ∨ (¬ p1225) ∨ (¬ p1256)) : (¬ p11) ∨ (¬ p13) ∨ (¬ p85) ∨ (¬ p576) ∨ (¬ p980) ∨ (¬ p1142) ∨ (¬ p1225) ∨ (¬ p1256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p129) := by
    exact h16154
  have u10 : p1184 := by
    exact h7053
  rcases h15310 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19870 (p2 p7 p142 p191 p207 p227 p435 p1335 p1452 : Prop)
    (h16152 : (¬ p7))
    (h15311 : (¬ p2) ∨ p7 ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p207) ∨ (¬ p227) ∨ (¬ p435) ∨ (¬ p1335) ∨ (¬ p1452)) : (¬ p2) ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p207) ∨ (¬ p227) ∨ (¬ p435) ∨ (¬ p1335) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p435 := by
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
  rcases h15311 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19871 (p6 p7 p38 p46 p101 p141 p288 : Prop)
    (h16152 : (¬ p7))
    (h15312 : (¬ p6) ∨ p7 ∨ (¬ p38) ∨ (¬ p46) ∨ (¬ p101) ∨ (¬ p141) ∨ (¬ p288)) : (¬ p6) ∨ (¬ p38) ∨ (¬ p46) ∨ (¬ p101) ∨ (¬ p141) ∨ (¬ p288) := by
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
  have u2 : p46 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15312 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19872 (p7 p8 p191 p206 p302 p343 p363 p690 p858 p1022 p1041 p1055 p1256 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h1950 : p343)
    (h15313 : p7 ∨ (¬ p8) ∨ (¬ p191) ∨ (¬ p206) ∨ p302 ∨ (¬ p343) ∨ (¬ p363) ∨ (¬ p690) ∨ (¬ p858) ∨ (¬ p1022) ∨ (¬ p1041) ∨ (¬ p1055) ∨ (¬ p1256)) : (¬ p8) ∨ (¬ p191) ∨ (¬ p206) ∨ (¬ p363) ∨ (¬ p690) ∨ (¬ p858) ∨ (¬ p1022) ∨ (¬ p1041) ∨ (¬ p1055) ∨ (¬ p1256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p363 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1041 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : (¬ p302) := by
    exact h16285
  have u12 : p343 := by
    exact h1950
  rcases h15313 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u11 q4)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)
  · exact False.elim (q12 u9)

theorem step19873 (p7 p128 p302 p435 p858 p1022 p1187 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16285 : (¬ p302))
    (h15314 : p7 ∨ (¬ p128) ∨ p302 ∨ (¬ p435) ∨ (¬ p858) ∨ (¬ p1022) ∨ (¬ p1187)) : (¬ p435) ∨ (¬ p858) ∨ (¬ p1022) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1022 := by
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
  rcases h15314 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19874 (p7 p14 p109 p161 p235 p1035 p1212 : Prop)
    (h16152 : (¬ p7))
    (h15315 : p7 ∨ (¬ p14) ∨ (¬ p109) ∨ (¬ p161) ∨ (¬ p235) ∨ (¬ p1035) ∨ (¬ p1212)) : (¬ p14) ∨ (¬ p109) ∨ (¬ p161) ∨ (¬ p235) ∨ (¬ p1035) ∨ (¬ p1212) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p235 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1212 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15315 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19875 (p7 p69 p225 p229 p303 p347 p406 p617 : Prop)
    (h16152 : (¬ p7))
    (h15316 : p7 ∨ (¬ p69) ∨ (¬ p225) ∨ (¬ p229) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p406) ∨ (¬ p617)) : (¬ p69) ∨ (¬ p225) ∨ (¬ p229) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p406) ∨ (¬ p617) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15316 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19876 (p230 p495 p575 p582 p1233 p1750 : Prop)
    (h16165 : (¬ p230))
    (h11312 : p1750)
    (h15317 : p230 ∨ (¬ p495) ∨ (¬ p575) ∨ p582 ∨ (¬ p1233) ∨ (¬ p1750)) : (¬ p495) ∨ (¬ p575) ∨ p582 ∨ (¬ p1233) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p575 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p582) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1233 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p230) := by
    exact h16165
  have u5 : p1750 := by
    exact h11312
  rcases h15317 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u2 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)

theorem step19877 (p2 p7 p45 p191 p801 p1393 : Prop)
    (h16152 : (¬ p7))
    (h15318 : (¬ p2) ∨ p7 ∨ (¬ p45) ∨ (¬ p191) ∨ (¬ p801) ∨ (¬ p1393)) : (¬ p2) ∨ (¬ p45) ∨ (¬ p191) ∨ (¬ p801) ∨ (¬ p1393) := by
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
  have u2 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p801 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15318 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19879 (p7 p14 p18 p142 p191 p226 : Prop)
    (h16152 : (¬ p7))
    (h15320 : p7 ∨ (¬ p14) ∨ (¬ p18) ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p226)) : (¬ p14) ∨ (¬ p18) ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p226) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15320 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19881 (p7 p129 p142 p207 p227 p980 p1139 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h6761 : p1139)
    (h15322 : p7 ∨ p129 ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p227) ∨ (¬ p980) ∨ (¬ p1139) ∨ (¬ p1452)) : (¬ p142) ∨ (¬ p207) ∨ (¬ p227) ∨ (¬ p980) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p1139 := by
    exact h6761
  rcases h15322 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step19882 (p7 p124 p129 p142 p207 p983 p1077 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h8348 : p1386)
    (h15323 : p7 ∨ (¬ p124) ∨ p129 ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p983) ∨ (¬ p1077) ∨ (¬ p1386)) : (¬ p124) ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p983) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p1386 := by
    exact h8348
  rcases h15323 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step19883 (p7 p18 p46 p141 p210 p1624 p1651 : Prop)
    (h16152 : (¬ p7))
    (h15326 : p7 ∨ (¬ p18) ∨ (¬ p46) ∨ (¬ p141) ∨ (¬ p210) ∨ (¬ p1624) ∨ (¬ p1651)) : (¬ p18) ∨ (¬ p46) ∨ (¬ p141) ∨ (¬ p210) ∨ (¬ p1624) ∨ (¬ p1651) := by
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
  have u2 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1651 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15326 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19884 (p2 p7 p127 p325 p349 p757 p1665 : Prop)
    (h16152 : (¬ p7))
    (h15327 : (¬ p2) ∨ p7 ∨ (¬ p127) ∨ (¬ p325) ∨ (¬ p349) ∨ (¬ p757) ∨ (¬ p1665)) : (¬ p2) ∨ (¬ p127) ∨ (¬ p325) ∨ (¬ p349) ∨ (¬ p757) ∨ (¬ p1665) := by
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
  have u2 : p325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p757 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15327 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19885 (p7 p16 p17 p595 p1286 p1333 p1454 p1644 : Prop)
    (h16152 : (¬ p7))
    (h15328 : p7 ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p595) ∨ (¬ p1286) ∨ (¬ p1333) ∨ (¬ p1454) ∨ (¬ p1644)) : (¬ p16) ∨ (¬ p17) ∨ (¬ p595) ∨ (¬ p1286) ∨ (¬ p1333) ∨ (¬ p1454) ∨ (¬ p1644) := by
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
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1286 := by
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
  have u6 : p1644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15328 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19886 (p2 p7 p875 p1035 p1135 p1140 p1325 : Prop)
    (h16152 : (¬ p7))
    (h16220 : (¬ p875))
    (h6744 : p1135)
    (h15329 : (¬ p2) ∨ p7 ∨ p875 ∨ (¬ p1035) ∨ (¬ p1135) ∨ (¬ p1140) ∨ (¬ p1325)) : (¬ p2) ∨ (¬ p1035) ∨ (¬ p1140) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p875) := by
    exact h16220
  have u6 : p1135 := by
    exact h6744
  rcases h15329 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19887 (p7 p8 p18 p104 p127 p128 p557 p667 p686 p983 p1004 p1159 p1325 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16205 : (¬ p686))
    (h15330 : p7 ∨ (¬ p8) ∨ (¬ p18) ∨ (¬ p104) ∨ (¬ p127) ∨ (¬ p128) ∨ (¬ p557) ∨ (¬ p667) ∨ p686 ∨ (¬ p983) ∨ (¬ p1004) ∨ (¬ p1159) ∨ (¬ p1325)) : (¬ p8) ∨ (¬ p18) ∨ (¬ p104) ∨ (¬ p127) ∨ (¬ p557) ∨ (¬ p667) ∨ (¬ p983) ∨ (¬ p1004) ∨ (¬ p1159) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : p128 := by
    exact h653
  have u12 : (¬ p686) := by
    exact h16205
  rcases h15330 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u12 q8)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)
  · exact False.elim (q12 u9)

theorem step19889 (p18 p67 p257 p659 : Prop)
    (h16170 : (¬ p257))
    (h3753 : p659)
    (h15333 : (¬ p18) ∨ p67 ∨ p257 ∨ (¬ p659)) : (¬ p18) ∨ p67 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p67) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p257) := by
    exact h16170
  have u3 : p659 := by
    exact h3753
  rcases h15333 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)

theorem step19890 (p5 p7 p665 p1095 p1096 p1159 p1333 p1465 : Prop)
    (h16152 : (¬ p7))
    (h15334 : (¬ p5) ∨ p7 ∨ (¬ p665) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1159) ∨ (¬ p1333) ∨ (¬ p1465)) : (¬ p5) ∨ (¬ p665) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1159) ∨ (¬ p1333) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15334 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19891 (p7 p142 p191 p225 p226 p329 p347 p438 p1366 : Prop)
    (h16152 : (¬ p7))
    (h15335 : p7 ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p329) ∨ (¬ p347) ∨ (¬ p438) ∨ (¬ p1366)) : (¬ p142) ∨ (¬ p191) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p329) ∨ (¬ p347) ∨ (¬ p438) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p191 := by
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
  have u4 : p329 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15335 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19893 (p323 p427 p1209 p1484 : Prop)
    (h2334 : p427)
    (h16345 : (¬ p1484))
    (h15337 : (¬ p323) ∨ (¬ p427) ∨ p1209 ∨ p1484) : (¬ p323) ∨ p1209 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1209) := fun hu => hn (Or.inr hu)
  have u2 : p427 := by
    exact h2334
  have u3 : (¬ p1484) := by
    exact h16345
  rcases h15337 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u3 q3)

theorem step19894 (p7 p11 p345 p438 p519 p1022 p1080 : Prop)
    (h16152 : (¬ p7))
    (h15338 : p7 ∨ (¬ p11) ∨ (¬ p345) ∨ (¬ p438) ∨ (¬ p519) ∨ (¬ p1022) ∨ (¬ p1080)) : (¬ p11) ∨ (¬ p345) ∨ (¬ p438) ∨ (¬ p519) ∨ (¬ p1022) ∨ (¬ p1080) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p519 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15338 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19895 (p7 p46 p142 p207 p368 p406 p1188 p1287 : Prop)
    (h16152 : (¬ p7))
    (h15339 : p7 ∨ (¬ p46) ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p1188) ∨ (¬ p1287)) : (¬ p46) ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p1188) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p46 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p207 := by
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
  rcases h15339 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19896 (p7 p19 p40 p85 p160 p207 p228 p236 p532 p858 p1184 p1385 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h7053 : p1184)
    (h15340 : p7 ∨ (¬ p19) ∨ p40 ∨ (¬ p85) ∨ (¬ p160) ∨ (¬ p207) ∨ (¬ p228) ∨ (¬ p236) ∨ (¬ p532) ∨ (¬ p858) ∨ (¬ p1184) ∨ (¬ p1385)) : (¬ p19) ∨ (¬ p85) ∨ (¬ p160) ∨ (¬ p207) ∨ (¬ p228) ∨ (¬ p236) ∨ (¬ p532) ∨ (¬ p858) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p236 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p40) := by
    exact h16150
  have u11 : p1184 := by
    exact h7053
  rcases h15340 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u10 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u11)
  · exact False.elim (q11 u8)

theorem step19897 (p6 p7 p19 p40 p481 p542 p616 p657 p1184 p1287 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h7053 : p1184)
    (h15342 : (¬ p6) ∨ p7 ∨ (¬ p19) ∨ p40 ∨ (¬ p481) ∨ (¬ p542) ∨ (¬ p616) ∨ (¬ p657) ∨ (¬ p1184) ∨ (¬ p1287)) : (¬ p6) ∨ (¬ p19) ∨ (¬ p481) ∨ (¬ p542) ∨ (¬ p616) ∨ (¬ p657) ∨ (¬ p1287) := by
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
  have u2 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p542 := by
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
  have u6 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p40) := by
    exact h16150
  have u9 : p1184 := by
    exact h7053
  rcases h15342 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u8 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u9)
  · exact False.elim (q9 u6)

theorem step19898 (p7 p83 p185 p303 p406 p521 p617 p928 p1385 : Prop)
    (h16152 : (¬ p7))
    (h15343 : p7 ∨ (¬ p83) ∨ (¬ p185) ∨ (¬ p303) ∨ (¬ p406) ∨ (¬ p521) ∨ (¬ p617) ∨ (¬ p928) ∨ (¬ p1385)) : (¬ p83) ∨ (¬ p185) ∨ (¬ p303) ∨ (¬ p406) ∨ (¬ p521) ∨ (¬ p617) ∨ (¬ p928) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p521 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15343 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19899 (p3 p7 p164 p983 p1159 p1181 p1465 : Prop)
    (h16152 : (¬ p7))
    (h789 : p164)
    (h16272 : (¬ p1181))
    (h15344 : (¬ p3) ∨ p7 ∨ (¬ p164) ∨ (¬ p983) ∨ (¬ p1159) ∨ p1181 ∨ (¬ p1465)) : (¬ p3) ∨ (¬ p983) ∨ (¬ p1159) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p983 := by
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
  have u5 : p164 := by
    exact h789
  have u6 : (¬ p1181) := by
    exact h16272
  rcases h15344 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step19900 (p6 p7 p19 p40 p224 p897 p1000 p1099 p1140 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h7053 : p1184)
    (h15345 : (¬ p6) ∨ p7 ∨ (¬ p19) ∨ p40 ∨ (¬ p224) ∨ (¬ p897) ∨ (¬ p1000) ∨ (¬ p1099) ∨ (¬ p1140) ∨ (¬ p1184)) : (¬ p6) ∨ (¬ p19) ∨ (¬ p224) ∨ (¬ p897) ∨ (¬ p1000) ∨ (¬ p1099) ∨ (¬ p1140) := by
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
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p40) := by
    exact h16150
  have u9 : p1184 := by
    exact h7053
  rcases h15345 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u8 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u9)

theorem step19901 (p7 p83 p185 p928 p1184 p1249 p1324 p1489 : Prop)
    (h16152 : (¬ p7))
    (h7053 : p1184)
    (h16309 : (¬ p1324))
    (h15346 : p7 ∨ (¬ p83) ∨ (¬ p185) ∨ (¬ p928) ∨ (¬ p1184) ∨ (¬ p1249) ∨ p1324 ∨ (¬ p1489)) : (¬ p83) ∨ (¬ p185) ∨ (¬ p928) ∨ (¬ p1249) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p1184 := by
    exact h7053
  have u7 : (¬ p1324) := by
    exact h16309
  rcases h15346 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step19902 (p7 p481 p542 p657 p998 p1159 : Prop)
    (h16152 : (¬ p7))
    (h15347 : p7 ∨ (¬ p481) ∨ (¬ p542) ∨ (¬ p657) ∨ (¬ p998) ∨ (¬ p1159)) : (¬ p481) ∨ (¬ p542) ∨ (¬ p657) ∨ (¬ p998) ∨ (¬ p1159) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p998 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15347 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19903 (p7 p19 p40 p160 p207 p236 p279 p532 p814 p1249 p1393 p1442 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h1444 : p279)
    (h15348 : p7 ∨ (¬ p19) ∨ p40 ∨ (¬ p160) ∨ (¬ p207) ∨ (¬ p236) ∨ (¬ p279) ∨ (¬ p532) ∨ (¬ p814) ∨ (¬ p1249) ∨ (¬ p1393) ∨ (¬ p1442)) : (¬ p19) ∨ (¬ p160) ∨ (¬ p207) ∨ (¬ p236) ∨ (¬ p532) ∨ (¬ p814) ∨ (¬ p1249) ∨ (¬ p1393) ∨ (¬ p1442) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p236 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1442 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p40) := by
    exact h16150
  have u11 : p279 := by
    exact h1444
  rcases h15348 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u10 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step19904 (p3 p6 p7 p129 p142 p172 p840 p897 p1099 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h7053 : p1184)
    (h15349 : (¬ p3) ∨ (¬ p6) ∨ p7 ∨ p129 ∨ (¬ p142) ∨ (¬ p172) ∨ (¬ p840) ∨ (¬ p897) ∨ (¬ p1099) ∨ (¬ p1184)) : (¬ p3) ∨ (¬ p6) ∨ (¬ p142) ∨ (¬ p172) ∨ (¬ p840) ∨ (¬ p897) ∨ (¬ p1099) := by
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
  have u2 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p840 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p129) := by
    exact h16154
  have u9 : p1184 := by
    exact h7053
  rcases h15349 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (u8 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u9)

theorem step19905 (p6 p7 p85 p129 p142 p481 p542 p836 p918 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h7053 : p1184)
    (h15350 : (¬ p6) ∨ p7 ∨ (¬ p85) ∨ p129 ∨ (¬ p142) ∨ (¬ p481) ∨ (¬ p542) ∨ (¬ p836) ∨ (¬ p918) ∨ (¬ p1184)) : (¬ p6) ∨ (¬ p85) ∨ (¬ p142) ∨ (¬ p481) ∨ (¬ p542) ∨ (¬ p836) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p129) := by
    exact h16154
  have u9 : p1184 := by
    exact h7053
  rcases h15350 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u8 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u9)

theorem step19906 (p7 p85 p303 p347 p406 p617 p836 p918 : Prop)
    (h16152 : (¬ p7))
    (h15351 : p7 ∨ (¬ p85) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p406) ∨ (¬ p617) ∨ (¬ p836) ∨ (¬ p918)) : (¬ p85) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p406) ∨ (¬ p617) ∨ (¬ p836) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15351 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19907 (p3 p7 p172 p1038 p1116 p1159 : Prop)
    (h16152 : (¬ p7))
    (h15352 : (¬ p3) ∨ p7 ∨ (¬ p172) ∨ (¬ p1038) ∨ (¬ p1116) ∨ (¬ p1159)) : (¬ p3) ∨ (¬ p172) ∨ (¬ p1038) ∨ (¬ p1116) ∨ (¬ p1159) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1038 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15352 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19908 (p6 p7 p129 p142 p1140 p1211 p1386 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h8348 : p1386)
    (h15353 : (¬ p6) ∨ p7 ∨ p129 ∨ (¬ p142) ∨ (¬ p1140) ∨ (¬ p1211) ∨ (¬ p1386) ∨ (¬ p1452)) : (¬ p6) ∨ (¬ p142) ∨ (¬ p1140) ∨ (¬ p1211) ∨ (¬ p1452) := by
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
  have u2 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p1386 := by
    exact h8348
  rcases h15353 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step19909 (p6 p7 p129 p142 p279 p1000 p1140 p1333 p1349 p1489 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h1444 : p279)
    (h15354 : (¬ p6) ∨ p7 ∨ p129 ∨ (¬ p142) ∨ (¬ p279) ∨ (¬ p1000) ∨ (¬ p1140) ∨ (¬ p1333) ∨ (¬ p1349) ∨ (¬ p1489)) : (¬ p6) ∨ (¬ p142) ∨ (¬ p1000) ∨ (¬ p1140) ∨ (¬ p1333) ∨ (¬ p1349) ∨ (¬ p1489) := by
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
  have u2 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p129) := by
    exact h16154
  have u9 : p279 := by
    exact h1444
  rcases h15354 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (u8 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step19910 (p7 p20 p46 p142 p1604 p1665 : Prop)
    (h16152 : (¬ p7))
    (h15355 : p7 ∨ (¬ p20) ∨ (¬ p46) ∨ (¬ p142) ∨ (¬ p1604) ∨ (¬ p1665)) : (¬ p20) ∨ (¬ p46) ∨ (¬ p142) ∨ (¬ p1604) ∨ (¬ p1665) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p20 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p46 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1604 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15355 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19911 (p7 p499 p710 p833 p858 p1103 p1325 p1449 p1611 : Prop)
    (h16152 : (¬ p7))
    (h15356 : p7 ∨ (¬ p499) ∨ (¬ p710) ∨ (¬ p833) ∨ (¬ p858) ∨ (¬ p1103) ∨ (¬ p1325) ∨ (¬ p1449) ∨ (¬ p1611)) : (¬ p499) ∨ (¬ p710) ∨ (¬ p833) ∨ (¬ p858) ∨ (¬ p1103) ∨ (¬ p1325) ∨ (¬ p1449) ∨ (¬ p1611) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p833 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1611 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15356 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19912 (p7 p16 p185 p303 p347 p595 p836 p1286 : Prop)
    (h16152 : (¬ p7))
    (h15357 : p7 ∨ (¬ p16) ∨ (¬ p185) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p595) ∨ (¬ p836) ∨ (¬ p1286)) : (¬ p16) ∨ (¬ p185) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p595) ∨ (¬ p836) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p347 := by
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
  have u6 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15357 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19913 (p7 p15 p234 p542 p836 p1055 p1103 p1116 : Prop)
    (h16152 : (¬ p7))
    (h15358 : p7 ∨ (¬ p15) ∨ (¬ p234) ∨ (¬ p542) ∨ (¬ p836) ∨ (¬ p1055) ∨ (¬ p1103) ∨ (¬ p1116)) : (¬ p15) ∨ (¬ p234) ∨ (¬ p542) ∨ (¬ p836) ∨ (¬ p1055) ∨ (¬ p1103) ∨ (¬ p1116) := by
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
  have u2 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p836 := by
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
  have u6 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15358 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19914 (p7 p16 p185 p499 p980 p1115 p1449 p1611 : Prop)
    (h16152 : (¬ p7))
    (h15359 : p7 ∨ (¬ p16) ∨ (¬ p185) ∨ (¬ p499) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p1449) ∨ (¬ p1611)) : (¬ p16) ∨ (¬ p185) ∨ (¬ p499) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p1449) ∨ (¬ p1611) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1611 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15359 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19915 (p7 p347 p499 p601 p836 p1055 p1103 p1116 : Prop)
    (h16152 : (¬ p7))
    (h15361 : p7 ∨ (¬ p347) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p836) ∨ (¬ p1055) ∨ (¬ p1103) ∨ (¬ p1116)) : (¬ p347) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p836) ∨ (¬ p1055) ∨ (¬ p1103) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p836 := by
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
  have u6 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15361 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19916 (p2 p7 p142 p191 p228 p532 p801 p858 p1035 p1212 : Prop)
    (h16152 : (¬ p7))
    (h15362 : (¬ p2) ∨ p7 ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p228) ∨ (¬ p532) ∨ (¬ p801) ∨ (¬ p858) ∨ (¬ p1035) ∨ (¬ p1212)) : (¬ p2) ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p228) ∨ (¬ p532) ∨ (¬ p801) ∨ (¬ p858) ∨ (¬ p1035) ∨ (¬ p1212) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p801 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1212 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15362 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19918 (p3 p7 p46 p229 p1159 p1256 : Prop)
    (h16152 : (¬ p7))
    (h15364 : (¬ p3) ∨ p7 ∨ (¬ p46) ∨ (¬ p229) ∨ (¬ p1159) ∨ (¬ p1256)) : (¬ p3) ∨ (¬ p46) ∨ (¬ p229) ∨ (¬ p1159) ∨ (¬ p1256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p46 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15364 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19919 (p2 p3 p7 p128 p229 p406 p430 p690 p1191 p1287 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16180 : (¬ p430))
    (h15365 : (¬ p2) ∨ (¬ p3) ∨ p7 ∨ (¬ p128) ∨ (¬ p229) ∨ (¬ p406) ∨ p430 ∨ (¬ p690) ∨ (¬ p1191) ∨ (¬ p1287)) : (¬ p2) ∨ (¬ p3) ∨ (¬ p229) ∨ (¬ p406) ∨ (¬ p690) ∨ (¬ p1191) ∨ (¬ p1287) := by
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
  have u2 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p128 := by
    exact h653
  have u9 : (¬ p430) := by
    exact h16180
  rcases h15365 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u9 q6)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step19920 (p7 p16 p185 p455 p499 p985 p1452 p1584 : Prop)
    (h16152 : (¬ p7))
    (h15366 : p7 ∨ (¬ p16) ∨ (¬ p185) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p985) ∨ (¬ p1452) ∨ (¬ p1584)) : (¬ p16) ∨ (¬ p185) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p985) ∨ (¬ p1452) ∨ (¬ p1584) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15366 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19921 (p7 p109 p134 p170 p560 p710 p840 : Prop)
    (h16152 : (¬ p7))
    (h15367 : p7 ∨ (¬ p109) ∨ (¬ p134) ∨ (¬ p170) ∨ (¬ p560) ∨ (¬ p710) ∨ (¬ p840)) : (¬ p109) ∨ (¬ p134) ∨ (¬ p170) ∨ (¬ p560) ∨ (¬ p710) ∨ (¬ p840) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15367 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19922 (p7 p16 p228 p532 p814 p858 p1225 p1229 : Prop)
    (h16152 : (¬ p7))
    (h15368 : p7 ∨ (¬ p16) ∨ (¬ p228) ∨ (¬ p532) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1225) ∨ (¬ p1229)) : (¬ p16) ∨ (¬ p228) ∨ (¬ p532) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1225) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p858 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15368 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19923 (p7 p16 p185 p227 p347 p456 p498 p601 p836 : Prop)
    (h16152 : (¬ p7))
    (h15370 : p7 ∨ (¬ p16) ∨ (¬ p185) ∨ (¬ p227) ∨ (¬ p347) ∨ (¬ p456) ∨ (¬ p498) ∨ (¬ p601) ∨ (¬ p836)) : (¬ p16) ∨ (¬ p185) ∨ (¬ p227) ∨ (¬ p347) ∨ (¬ p456) ∨ (¬ p498) ∨ (¬ p601) ∨ (¬ p836) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15370 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19924 (p7 p16 p185 p224 p228 p455 p499 p836 : Prop)
    (h16152 : (¬ p7))
    (h15371 : p7 ∨ (¬ p16) ∨ (¬ p185) ∨ (¬ p224) ∨ (¬ p228) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p836)) : (¬ p16) ∨ (¬ p185) ∨ (¬ p224) ∨ (¬ p228) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p836) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
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
  have u4 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15371 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19925 (p7 p87 p185 p224 p227 p228 p262 p581 p836 : Prop)
    (h16152 : (¬ p7))
    (h15372 : p7 ∨ (¬ p87) ∨ (¬ p185) ∨ (¬ p224) ∨ (¬ p227) ∨ (¬ p228) ∨ (¬ p262) ∨ (¬ p581) ∨ (¬ p836)) : (¬ p87) ∨ (¬ p185) ∨ (¬ p224) ∨ (¬ p227) ∨ (¬ p228) ∨ (¬ p262) ∨ (¬ p581) ∨ (¬ p836) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
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
  have u5 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15372 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19926 (p7 p63 p303 p347 p406 p615 p897 p1099 p1389 : Prop)
    (h16152 : (¬ p7))
    (h15373 : p7 ∨ (¬ p63) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p406) ∨ (¬ p615) ∨ (¬ p897) ∨ (¬ p1099) ∨ (¬ p1389)) : (¬ p63) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p406) ∨ (¬ p615) ∨ (¬ p897) ∨ (¬ p1099) ∨ (¬ p1389) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p615 := by
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
  have u7 : p1389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15373 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19927 (p7 p87 p185 p262 p303 p347 p368 p406 p581 p897 p926 : Prop)
    (h16152 : (¬ p7))
    (h15374 : p7 ∨ (¬ p87) ∨ (¬ p185) ∨ (¬ p262) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p581) ∨ (¬ p897) ∨ (¬ p926)) : (¬ p87) ∨ (¬ p185) ∨ (¬ p262) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p581) ∨ (¬ p897) ∨ (¬ p926) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h15374 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19928 (p2 p257 p330 p659 : Prop)
    (h16170 : (¬ p257))
    (h3753 : p659)
    (h15375 : (¬ p2) ∨ p257 ∨ p330 ∨ (¬ p659)) : (¬ p2) ∨ p330 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p330) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p257) := by
    exact h16170
  have u3 : p659 := by
    exact h3753
  rcases h15375 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)

theorem step19929 (p7 p225 p226 p659 p840 p1115 p1181 : Prop)
    (h16152 : (¬ p7))
    (h3753 : p659)
    (h16272 : (¬ p1181))
    (h15377 : p7 ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p659) ∨ (¬ p840) ∨ (¬ p1115) ∨ p1181) : (¬ p225) ∨ (¬ p226) ∨ (¬ p840) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p659 := by
    exact h3753
  have u6 : (¬ p1181) := by
    exact h16272
  rcases h15377 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step19931 (p7 p134 p257 p303 p345 p406 p424 p476 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h6478 : p1075)
    (h15379 : p7 ∨ (¬ p134) ∨ p257 ∨ (¬ p303) ∨ (¬ p345) ∨ (¬ p406) ∨ (¬ p424) ∨ (¬ p476) ∨ (¬ p1075)) : (¬ p134) ∨ (¬ p303) ∨ (¬ p345) ∨ (¬ p406) ∨ (¬ p424) ∨ (¬ p476) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p476 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p257) := by
    exact h16170
  have u8 : p1075 := by
    exact h6478
  rcases h15379 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u8)

theorem step19932 (p7 p167 p189 p225 p263 p303 p347 p368 p406 : Prop)
    (h16152 : (¬ p7))
    (h15380 : p7 ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p225) ∨ (¬ p263) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p368) ∨ (¬ p406)) : (¬ p167) ∨ (¬ p189) ∨ (¬ p225) ∨ (¬ p263) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p368) ∨ (¬ p406) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p263 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15380 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19933 (p7 p161 p457 p633 p1080 p1452 : Prop)
    (h16152 : (¬ p7))
    (h15382 : p7 ∨ (¬ p161) ∨ (¬ p457) ∨ (¬ p633) ∨ (¬ p1080) ∨ (¬ p1452)) : (¬ p161) ∨ (¬ p457) ∨ (¬ p633) ∨ (¬ p1080) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p457 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15382 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19934 (p7 p121 p257 p362 p420 p961 p1530 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h9352 : p1530)
    (h15383 : p7 ∨ (¬ p121) ∨ p257 ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p961) ∨ (¬ p1530)) : (¬ p121) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p961) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p121 := by
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
  have u3 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p257) := by
    exact h16170
  have u6 : p1530 := by
    exact h9352
  rcases h15383 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19935 (p7 p185 p279 p544 p836 p1036 p1181 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16272 : (¬ p1181))
    (h15384 : p7 ∨ (¬ p185) ∨ (¬ p279) ∨ (¬ p544) ∨ (¬ p836) ∨ (¬ p1036) ∨ p1181) : (¬ p185) ∨ (¬ p544) ∨ (¬ p836) ∨ (¬ p1036) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p279 := by
    exact h1444
  have u6 : (¬ p1181) := by
    exact h16272
  rcases h15384 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step19936 (p7 p12 p63 p108 p257 p792 p1074 p1099 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h4535 : p792)
    (h15385 : p7 ∨ (¬ p12) ∨ (¬ p63) ∨ (¬ p108) ∨ p257 ∨ (¬ p792) ∨ (¬ p1074) ∨ (¬ p1099)) : (¬ p12) ∨ (¬ p63) ∨ (¬ p108) ∨ (¬ p1074) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p257) := by
    exact h16170
  have u7 : p792 := by
    exact h4535
  rcases h15385 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step19937 (p7 p124 p138 p185 p193 p262 p344 p664 p1115 : Prop)
    (h16152 : (¬ p7))
    (h15386 : p7 ∨ (¬ p124) ∨ (¬ p138) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p262) ∨ (¬ p344) ∨ (¬ p664) ∨ (¬ p1115)) : (¬ p124) ∨ (¬ p138) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p262) ∨ (¬ p344) ∨ (¬ p664) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15386 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19938 (p7 p17 p230 p581 p1346 p1386 p1452 p1495 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h8348 : p1386)
    (h15387 : p7 ∨ (¬ p17) ∨ p230 ∨ (¬ p581) ∨ (¬ p1346) ∨ (¬ p1386) ∨ (¬ p1452) ∨ (¬ p1495)) : (¬ p17) ∨ (¬ p581) ∨ (¬ p1346) ∨ (¬ p1452) ∨ (¬ p1495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p1386 := by
    exact h8348
  rcases h15387 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step19939 (p7 p17 p123 p980 p1139 p1346 p1508 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h6761 : p1139)
    (h15388 : p7 ∨ (¬ p17) ∨ p123 ∨ (¬ p980) ∨ (¬ p1139) ∨ (¬ p1346) ∨ (¬ p1508)) : (¬ p17) ∨ (¬ p980) ∨ (¬ p1346) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p123) := by
    exact h16186
  have u6 : p1139 := by
    exact h6761
  rcases h15388 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19940 (p7 p138 p193 p262 p368 p384 p406 p980 p1124 p1349 p1452 : Prop)
    (h16152 : (¬ p7))
    (h15389 : p7 ∨ (¬ p138) ∨ (¬ p193) ∨ (¬ p262) ∨ (¬ p368) ∨ (¬ p384) ∨ (¬ p406) ∨ (¬ p980) ∨ (¬ p1124) ∨ (¬ p1349) ∨ (¬ p1452)) : (¬ p138) ∨ (¬ p193) ∨ (¬ p262) ∨ (¬ p368) ∨ (¬ p384) ∨ (¬ p406) ∨ (¬ p980) ∨ (¬ p1124) ∨ (¬ p1349) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p193 := by
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
  have u4 : p384 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p406 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h15389 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19941 (p7 p193 p798 p814 p1373 p1713 : Prop)
    (h16152 : (¬ p7))
    (h15390 : p7 ∨ (¬ p193) ∨ (¬ p798) ∨ (¬ p814) ∨ (¬ p1373) ∨ (¬ p1713)) : (¬ p193) ∨ (¬ p798) ∨ (¬ p814) ∨ (¬ p1373) ∨ (¬ p1713) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p798 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1373 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1713 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15390 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19942 (p7 p23 p125 p134 p328 p424 p425 : Prop)
    (h16152 : (¬ p7))
    (h15391 : p7 ∨ (¬ p23) ∨ (¬ p125) ∨ (¬ p134) ∨ (¬ p328) ∨ (¬ p424) ∨ (¬ p425)) : (¬ p23) ∨ (¬ p125) ∨ (¬ p134) ∨ (¬ p328) ∨ (¬ p424) ∨ (¬ p425) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p328 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15391 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19943 (p2 p5 p7 p422 p424 p1044 p1095 p1096 : Prop)
    (h16152 : (¬ p7))
    (h15392 : (¬ p2) ∨ (¬ p5) ∨ p7 ∨ (¬ p422) ∨ (¬ p424) ∨ (¬ p1044) ∨ (¬ p1095) ∨ (¬ p1096)) : (¬ p2) ∨ (¬ p5) ∨ (¬ p422) ∨ (¬ p424) ∨ (¬ p1044) ∨ (¬ p1095) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1044 := by
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
  rcases h15392 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19945 (p7 p63 p160 p228 p236 p421 p532 p577 p616 p1287 : Prop)
    (h16152 : (¬ p7))
    (h15394 : p7 ∨ (¬ p63) ∨ (¬ p160) ∨ (¬ p228) ∨ (¬ p236) ∨ (¬ p421) ∨ (¬ p532) ∨ (¬ p577) ∨ (¬ p616) ∨ (¬ p1287)) : (¬ p63) ∨ (¬ p160) ∨ (¬ p228) ∨ (¬ p236) ∨ (¬ p421) ∨ (¬ p532) ∨ (¬ p577) ∨ (¬ p616) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p236 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15394 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19946 (p7 p344 p532 p664 p983 p1078 : Prop)
    (h16152 : (¬ p7))
    (h15395 : p7 ∨ (¬ p344) ∨ (¬ p532) ∨ (¬ p664) ∨ (¬ p983) ∨ (¬ p1078)) : (¬ p344) ∨ (¬ p532) ∨ (¬ p664) ∨ (¬ p983) ∨ (¬ p1078) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1078 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15395 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19947 (p2 p7 p88 p134 p188 p257 p424 p461 p495 p577 p1229 p1386 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h8348 : p1386)
    (h15396 : (¬ p2) ∨ p7 ∨ (¬ p88) ∨ (¬ p134) ∨ (¬ p188) ∨ p257 ∨ (¬ p424) ∨ (¬ p461) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1229) ∨ (¬ p1386) ∨ (¬ p1452)) : (¬ p2) ∨ (¬ p88) ∨ (¬ p134) ∨ (¬ p188) ∨ (¬ p424) ∨ (¬ p461) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1229) ∨ (¬ p1452) := by
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
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p461 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : (¬ p257) := by
    exact h16170
  have u12 : p1386 := by
    exact h8348
  rcases h15396 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (q0 u0)
  · exact False.elim (u10 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u11 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u8)
  · exact False.elim (q11 u12)
  · exact False.elim (q12 u9)

theorem step19948 (p2 p5 p7 p23 p124 p134 p424 p498 p636 : Prop)
    (h16152 : (¬ p7))
    (h15397 : (¬ p2) ∨ (¬ p5) ∨ p7 ∨ (¬ p23) ∨ (¬ p124) ∨ (¬ p134) ∨ (¬ p424) ∨ (¬ p498) ∨ (¬ p636)) : (¬ p2) ∨ (¬ p5) ∨ (¬ p23) ∨ (¬ p124) ∨ (¬ p134) ∨ (¬ p424) ∨ (¬ p498) ∨ (¬ p636) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15397 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u8 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19949 (p7 p121 p160 p161 p257 p343 p904 p960 p1306 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h1950 : p343)
    (h15398 : p7 ∨ (¬ p121) ∨ (¬ p160) ∨ (¬ p161) ∨ p257 ∨ (¬ p343) ∨ (¬ p904) ∨ (¬ p960) ∨ (¬ p1306)) : (¬ p121) ∨ (¬ p160) ∨ (¬ p161) ∨ (¬ p904) ∨ (¬ p960) ∨ (¬ p1306) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p121 := by
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
  have u3 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p960 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p257) := by
    exact h16170
  have u8 : p343 := by
    exact h1950
  rcases h15398 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step19950 (p7 p279 p302 p303 p434 p814 p1015 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16285 : (¬ p302))
    (h15399 : p7 ∨ (¬ p279) ∨ p302 ∨ (¬ p303) ∨ (¬ p434) ∨ (¬ p814) ∨ (¬ p1015)) : (¬ p303) ∨ (¬ p434) ∨ (¬ p814) ∨ (¬ p1015) := by
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
  have u5 : p279 := by
    exact h1444
  have u6 : (¬ p302) := by
    exact h16285
  rcases h15399 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19951 (p7 p23 p456 p532 p1035 p1212 : Prop)
    (h16152 : (¬ p7))
    (h15400 : p7 ∨ (¬ p23) ∨ (¬ p456) ∨ (¬ p532) ∨ (¬ p1035) ∨ (¬ p1212)) : (¬ p23) ∨ (¬ p456) ∨ (¬ p532) ∨ (¬ p1035) ∨ (¬ p1212) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1212 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15400 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19952 (p7 p161 p227 p343 p498 p904 p1136 p1306 p1452 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16259 : (¬ p1136))
    (h15401 : p7 ∨ (¬ p161) ∨ (¬ p227) ∨ (¬ p343) ∨ (¬ p498) ∨ (¬ p904) ∨ p1136 ∨ (¬ p1306) ∨ (¬ p1452)) : (¬ p161) ∨ (¬ p227) ∨ (¬ p498) ∨ (¬ p904) ∨ (¬ p1306) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : p343 := by
    exact h1950
  have u8 : (¬ p1136) := by
    exact h16259
  rcases h15401 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u8 q6)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step19953 (p7 p303 p427 p595 p919 p1099 p1286 : Prop)
    (h16152 : (¬ p7))
    (h2334 : p427)
    (h16230 : (¬ p919))
    (h15402 : p7 ∨ (¬ p303) ∨ (¬ p427) ∨ (¬ p595) ∨ p919 ∨ (¬ p1099) ∨ (¬ p1286)) : (¬ p303) ∨ (¬ p595) ∨ (¬ p1099) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p427 := by
    exact h2334
  have u6 : (¬ p919) := by
    exact h16230
  rcases h15402 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19955 (p7 p14 p83 p160 p188 p226 p1004 p1141 p1233 p1325 : Prop)
    (h16152 : (¬ p7))
    (h15404 : p7 ∨ (¬ p14) ∨ (¬ p83) ∨ (¬ p160) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p1004) ∨ (¬ p1141) ∨ (¬ p1233) ∨ (¬ p1325)) : (¬ p14) ∨ (¬ p83) ∨ (¬ p160) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p1004) ∨ (¬ p1141) ∨ (¬ p1233) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p226 := by
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
  have u7 : p1233 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15404 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19956 (p7 p16 p189 p224 p545 p796 p903 p1096 p1286 : Prop)
    (h16152 : (¬ p7))
    (h15406 : p7 ∨ (¬ p16) ∨ (¬ p189) ∨ (¬ p224) ∨ (¬ p545) ∨ (¬ p796) ∨ (¬ p903) ∨ (¬ p1096) ∨ (¬ p1286)) : (¬ p16) ∨ (¬ p189) ∨ (¬ p224) ∨ (¬ p545) ∨ (¬ p796) ∨ (¬ p903) ∨ (¬ p1096) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p903 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15406 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19957 (p7 p102 p209 p305 p1055 p1077 : Prop)
    (h16152 : (¬ p7))
    (h15407 : p7 ∨ (¬ p102) ∨ (¬ p209) ∨ (¬ p305) ∨ (¬ p1055) ∨ (¬ p1077)) : (¬ p102) ∨ (¬ p209) ∨ (¬ p305) ∨ (¬ p1055) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15407 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19959 (p7 p45 p85 p224 p406 p545 p617 p796 : Prop)
    (h16152 : (¬ p7))
    (h15409 : p7 ∨ (¬ p45) ∨ (¬ p85) ∨ (¬ p224) ∨ (¬ p406) ∨ (¬ p545) ∨ (¬ p617) ∨ (¬ p796)) : (¬ p45) ∨ (¬ p85) ∨ (¬ p224) ∨ (¬ p406) ∨ (¬ p545) ∨ (¬ p617) ∨ (¬ p796) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p85 := by
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
  have u5 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15409 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19960 (p7 p8 p45 p85 p102 p257 p306 p422 p657 p1004 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h7053 : p1184)
    (h15410 : p7 ∨ (¬ p8) ∨ (¬ p45) ∨ (¬ p85) ∨ (¬ p102) ∨ p257 ∨ (¬ p306) ∨ (¬ p422) ∨ (¬ p657) ∨ (¬ p1004) ∨ (¬ p1184)) : (¬ p8) ∨ (¬ p45) ∨ (¬ p85) ∨ (¬ p102) ∨ (¬ p306) ∨ (¬ p422) ∨ (¬ p657) ∨ (¬ p1004) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p257) := by
    exact h16170
  have u10 : p1184 := by
    exact h7053
  rcases h15410 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u9 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u10)

theorem step19961 (p7 p44 p63 p69 p167 p792 p1036 p1181 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16272 : (¬ p1181))
    (h15411 : p7 ∨ (¬ p44) ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p167) ∨ (¬ p792) ∨ (¬ p1036) ∨ p1181) : (¬ p44) ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p167) ∨ (¬ p1036) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p792 := by
    exact h4535
  have u7 : (¬ p1181) := by
    exact h16272
  rcases h15411 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step19962 (p7 p88 p124 p167 p189 p498 p616 p636 p1036 p1181 p1389 p1530 : Prop)
    (h16152 : (¬ p7))
    (h16272 : (¬ p1181))
    (h9352 : p1530)
    (h15412 : p7 ∨ (¬ p88) ∨ (¬ p124) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p498) ∨ (¬ p616) ∨ (¬ p636) ∨ (¬ p1036) ∨ p1181 ∨ (¬ p1389) ∨ (¬ p1530)) : (¬ p88) ∨ (¬ p124) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p498) ∨ (¬ p616) ∨ (¬ p636) ∨ (¬ p1036) ∨ (¬ p1389) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p1181) := by
    exact h16272
  have u11 : p1530 := by
    exact h9352
  rcases h15412 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (u10 q9)
  · exact False.elim (q10 u8)
  · exact False.elim (q11 u11)

theorem step19963 (p7 p16 p163 p188 p226 p422 p595 p1004 p1286 : Prop)
    (h16152 : (¬ p7))
    (h15413 : p7 ∨ (¬ p16) ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p422) ∨ (¬ p595) ∨ (¬ p1004) ∨ (¬ p1286)) : (¬ p16) ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p422) ∨ (¬ p595) ∨ (¬ p1004) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15413 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19964 (p7 p85 p257 p323 p364 p406 p918 p985 p1184 p1333 p1584 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h7053 : p1184)
    (h15414 : p7 ∨ (¬ p85) ∨ p257 ∨ (¬ p323) ∨ (¬ p364) ∨ (¬ p406) ∨ (¬ p918) ∨ (¬ p985) ∨ (¬ p1184) ∨ (¬ p1333) ∨ (¬ p1584)) : (¬ p85) ∨ (¬ p323) ∨ (¬ p364) ∨ (¬ p406) ∨ (¬ p918) ∨ (¬ p985) ∨ (¬ p1333) ∨ (¬ p1584) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
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
  have u4 : p918 := by
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
  have u7 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p257) := by
    exact h16170
  have u10 : p1184 := by
    exact h7053
  rcases h15414 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u9 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step19965 (p7 p8 p45 p85 p134 p257 p657 p1100 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h8348 : p1386)
    (h15415 : p7 ∨ (¬ p8) ∨ (¬ p45) ∨ (¬ p85) ∨ (¬ p134) ∨ p257 ∨ (¬ p657) ∨ (¬ p1100) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p8) ∨ (¬ p45) ∨ (¬ p85) ∨ (¬ p134) ∨ (¬ p657) ∨ (¬ p1100) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1100 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p257) := by
    exact h16170
  have u9 : p1386 := by
    exact h8348
  rcases h15415 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19966 (p7 p8 p41 p83 p123 p189 p576 p657 p1100 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h8348 : p1386)
    (h15416 : p7 ∨ (¬ p8) ∨ (¬ p41) ∨ (¬ p83) ∨ p123 ∨ (¬ p189) ∨ (¬ p576) ∨ (¬ p657) ∨ (¬ p1100) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p8) ∨ (¬ p41) ∨ (¬ p83) ∨ (¬ p189) ∨ (¬ p576) ∨ (¬ p657) ∨ (¬ p1100) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
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
  have u6 : p1100 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p123) := by
    exact h16186
  have u10 : p1386 := by
    exact h8348
  rcases h15416 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19967 (p7 p17 p42 p193 p257 p301 p323 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16170 : (¬ p257))
    (h15417 : p7 ∨ (¬ p17) ∨ (¬ p42) ∨ (¬ p193) ∨ p257 ∨ (¬ p301) ∨ (¬ p323)) : (¬ p17) ∨ (¬ p193) ∨ (¬ p301) ∨ (¬ p323) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p42 := by
    exact h132
  have u6 : (¬ p257) := by
    exact h16170
  rcases h15417 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19968 (p7 p45 p85 p125 p227 p257 p323 p422 p1184 p1214 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h7053 : p1184)
    (h15418 : p7 ∨ (¬ p45) ∨ (¬ p85) ∨ (¬ p125) ∨ (¬ p227) ∨ p257 ∨ (¬ p323) ∨ (¬ p422) ∨ (¬ p1184) ∨ (¬ p1214)) : (¬ p45) ∨ (¬ p85) ∨ (¬ p125) ∨ (¬ p227) ∨ (¬ p323) ∨ (¬ p422) ∨ (¬ p1214) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1214 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p257) := by
    exact h16170
  have u9 : p1184 := by
    exact h7053
  rcases h15418 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u8 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u9)
  · exact False.elim (q9 u6)

theorem step19970 (p7 p122 p134 p257 p532 p1035 p1256 : Prop)
    (h16152 : (¬ p7))
    (h10260 : p122)
    (h16170 : (¬ p257))
    (h15420 : p7 ∨ (¬ p122) ∨ (¬ p134) ∨ p257 ∨ (¬ p532) ∨ (¬ p1035) ∨ (¬ p1256)) : (¬ p134) ∨ (¬ p532) ∨ (¬ p1035) ∨ (¬ p1256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p122 := by
    exact h10260
  have u6 : (¬ p257) := by
    exact h16170
  rcases h15420 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19972 (p3 p6 p7 p128 p129 p142 p229 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16154 : (¬ p129))
    (h15422 : (¬ p3) ∨ (¬ p6) ∨ p7 ∨ (¬ p128) ∨ p129 ∨ (¬ p142) ∨ (¬ p229)) : (¬ p3) ∨ (¬ p6) ∨ (¬ p142) ∨ (¬ p229) := by
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
  have u2 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p128 := by
    exact h653
  have u6 : (¬ p129) := by
    exact h16154
  rcases h15422 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u4 q2)
  · exact False.elim (q3 u5)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19973 (p7 p224 p228 p532 p710 p1103 p1225 p1229 : Prop)
    (h16152 : (¬ p7))
    (h15423 : p7 ∨ (¬ p224) ∨ (¬ p228) ∨ (¬ p532) ∨ (¬ p710) ∨ (¬ p1103) ∨ (¬ p1225) ∨ (¬ p1229)) : (¬ p224) ∨ (¬ p228) ∨ (¬ p532) ∨ (¬ p710) ∨ (¬ p1103) ∨ (¬ p1225) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1103 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15423 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19974 (p3 p6 p7 p107 p129 p142 p756 p1603 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h9837 : p1603)
    (h15424 : (¬ p3) ∨ (¬ p6) ∨ p7 ∨ (¬ p107) ∨ p129 ∨ (¬ p142) ∨ (¬ p756) ∨ (¬ p1603)) : (¬ p3) ∨ (¬ p6) ∨ (¬ p107) ∨ (¬ p142) ∨ (¬ p756) := by
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
  have u2 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p1603 := by
    exact h9837
  rcases h15424 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step19975 (p6 p7 p129 p142 p535 p710 p840 p1040 p1115 p1140 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h2985 : p535)
    (h15425 : (¬ p6) ∨ p7 ∨ p129 ∨ (¬ p142) ∨ (¬ p535) ∨ (¬ p710) ∨ (¬ p840) ∨ (¬ p1040) ∨ (¬ p1115) ∨ (¬ p1140)) : (¬ p6) ∨ (¬ p142) ∨ (¬ p710) ∨ (¬ p840) ∨ (¬ p1040) ∨ (¬ p1115) ∨ (¬ p1140) := by
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
  have u2 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1040 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p129) := by
    exact h16154
  have u9 : p535 := by
    exact h2985
  rcases h15425 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (u8 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step19976 (p7 p535 p710 p840 p980 p1115 p1324 : Prop)
    (h16152 : (¬ p7))
    (h2985 : p535)
    (h16309 : (¬ p1324))
    (h15426 : p7 ∨ (¬ p535) ∨ (¬ p710) ∨ (¬ p840) ∨ (¬ p980) ∨ (¬ p1115) ∨ p1324) : (¬ p710) ∨ (¬ p840) ∨ (¬ p980) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p535 := by
    exact h2985
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h15426 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step19977 (p6 p7 p191 p424 p532 p1206 p1330 p1366 : Prop)
    (h16152 : (¬ p7))
    (h15427 : (¬ p6) ∨ p7 ∨ (¬ p191) ∨ (¬ p424) ∨ (¬ p532) ∨ (¬ p1206) ∨ (¬ p1330) ∨ (¬ p1366)) : (¬ p6) ∨ (¬ p191) ∨ (¬ p424) ∨ (¬ p532) ∨ (¬ p1206) ∨ (¬ p1330) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p191 := by
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
  have u4 : p1206 := by
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
  rcases h15427 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19978 (p7 p185 p255 p256 p757 p1651 : Prop)
    (h16152 : (¬ p7))
    (h15429 : p7 ∨ (¬ p185) ∨ (¬ p255) ∨ (¬ p256) ∨ (¬ p757) ∨ (¬ p1651)) : (¬ p185) ∨ (¬ p255) ∨ (¬ p256) ∨ (¬ p757) ∨ (¬ p1651) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p757 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1651 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15429 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19979 (p7 p162 p185 p224 p343 p789 p790 : Prop)
    (h16152 : (¬ p7))
    (h16160 : (¬ p162))
    (h1950 : p343)
    (h15430 : p7 ∨ p162 ∨ (¬ p185) ∨ (¬ p224) ∨ (¬ p343) ∨ (¬ p789) ∨ (¬ p790)) : (¬ p185) ∨ (¬ p224) ∨ (¬ p789) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
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
  have u3 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p162) := by
    exact h16160
  have u6 : p343 := by
    exact h1950
  rcases h15430 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19980 (p7 p134 p189 p224 p351 p386 p406 p817 p1206 : Prop)
    (h16152 : (¬ p7))
    (h15431 : p7 ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p224) ∨ (¬ p351) ∨ (¬ p386) ∨ (¬ p406) ∨ (¬ p817) ∨ (¬ p1206)) : (¬ p134) ∨ (¬ p189) ∨ (¬ p224) ∨ (¬ p351) ∨ (¬ p386) ∨ (¬ p406) ∨ (¬ p817) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p386 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p817 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15431 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19982 (p7 p41 p156 p158 p406 p680 p1287 p1387 : Prop)
    (h16152 : (¬ p7))
    (h15433 : p7 ∨ (¬ p41) ∨ (¬ p156) ∨ (¬ p158) ∨ (¬ p406) ∨ (¬ p680) ∨ (¬ p1287) ∨ (¬ p1387)) : (¬ p41) ∨ (¬ p156) ∨ (¬ p158) ∨ (¬ p406) ∨ (¬ p680) ∨ (¬ p1287) ∨ (¬ p1387) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p680 := by
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
  rcases h15433 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19983 (p7 p18 p69 p224 p351 p386 p406 p680 p1100 p1206 : Prop)
    (h16152 : (¬ p7))
    (h15434 : p7 ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p224) ∨ (¬ p351) ∨ (¬ p386) ∨ (¬ p406) ∨ (¬ p680) ∨ (¬ p1100) ∨ (¬ p1206)) : (¬ p18) ∨ (¬ p69) ∨ (¬ p224) ∨ (¬ p351) ∨ (¬ p386) ∨ (¬ p406) ∨ (¬ p680) ∨ (¬ p1100) ∨ (¬ p1206) := by
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
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p386 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1100 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15434 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19985 (p7 p224 p685 p728 p903 p1096 p1136 p1286 : Prop)
    (h16152 : (¬ p7))
    (h3898 : p685)
    (h16259 : (¬ p1136))
    (h15436 : p7 ∨ (¬ p224) ∨ (¬ p685) ∨ (¬ p728) ∨ (¬ p903) ∨ (¬ p1096) ∨ p1136 ∨ (¬ p1286)) : (¬ p224) ∨ (¬ p728) ∨ (¬ p903) ∨ (¬ p1096) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p903 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p685 := by
    exact h3898
  have u7 : (¬ p1136) := by
    exact h16259
  rcases h15436 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step19986 (p7 p224 p351 p386 p1325 p1452 : Prop)
    (h16152 : (¬ p7))
    (h15437 : p7 ∨ (¬ p224) ∨ (¬ p351) ∨ (¬ p386) ∨ (¬ p1325) ∨ (¬ p1452)) : (¬ p224) ∨ (¬ p351) ∨ (¬ p386) ∨ (¬ p1325) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p351 := by
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
  have u4 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15437 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19987 (p7 p161 p406 p622 p1288 p1333 : Prop)
    (h16152 : (¬ p7))
    (h15438 : p7 ∨ (¬ p161) ∨ (¬ p406) ∨ (¬ p622) ∨ (¬ p1288) ∨ (¬ p1333)) : (¬ p161) ∨ (¬ p406) ∨ (¬ p622) ∨ (¬ p1288) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p622 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15438 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19988 (p7 p8 p88 p134 p189 p389 p657 p924 p1098 p1206 : Prop)
    (h16152 : (¬ p7))
    (h15439 : p7 ∨ (¬ p8) ∨ (¬ p88) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p389) ∨ (¬ p657) ∨ (¬ p924) ∨ (¬ p1098) ∨ (¬ p1206)) : (¬ p8) ∨ (¬ p88) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p389) ∨ (¬ p657) ∨ (¬ p924) ∨ (¬ p1098) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p389 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15439 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19989 (p7 p15 p128 p495 p544 p634 p653 p897 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16194 : (¬ p653))
    (h15440 : p7 ∨ (¬ p15) ∨ (¬ p128) ∨ (¬ p495) ∨ (¬ p544) ∨ (¬ p634) ∨ p653 ∨ (¬ p897)) : (¬ p15) ∨ (¬ p495) ∨ (¬ p544) ∨ (¬ p634) ∨ (¬ p897) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p634 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p128 := by
    exact h653
  have u7 : (¬ p653) := by
    exact h16194
  rcases h15440 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step19990 (p7 p16 p134 p189 p389 p595 p1206 p1286 : Prop)
    (h16152 : (¬ p7))
    (h15441 : p7 ∨ (¬ p16) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p389) ∨ (¬ p595) ∨ (¬ p1206) ∨ (¬ p1286)) : (¬ p16) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p389) ∨ (¬ p595) ∨ (¬ p1206) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15441 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19991 (p7 p88 p258 p261 p686 p924 p961 p983 p1099 p1229 p1310 p1386 p1443 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h8348 : p1386)
    (h15442 : p7 ∨ (¬ p88) ∨ (¬ p258) ∨ (¬ p261) ∨ p686 ∨ (¬ p924) ∨ (¬ p961) ∨ (¬ p983) ∨ (¬ p1099) ∨ (¬ p1229) ∨ (¬ p1310) ∨ (¬ p1386) ∨ (¬ p1443)) : (¬ p88) ∨ (¬ p258) ∨ (¬ p261) ∨ (¬ p924) ∨ (¬ p961) ∨ (¬ p983) ∨ (¬ p1099) ∨ (¬ p1229) ∨ (¬ p1310) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
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
  have u3 : p924 := by
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
  have u6 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1310 := by
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
  have u12 : p1386 := by
    exact h8348
  rcases h15442 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
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
  · exact False.elim (q11 u12)
  · exact False.elim (q12 u9)

theorem step19992 (p7 p258 p686 p1135 p1325 p1443 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h6744 : p1135)
    (h15443 : p7 ∨ (¬ p258) ∨ p686 ∨ (¬ p1135) ∨ (¬ p1325) ∨ (¬ p1443) ∨ (¬ p1452)) : (¬ p258) ∨ (¬ p1325) ∨ (¬ p1443) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p686) := by
    exact h16205
  have u6 : p1135 := by
    exact h6744
  rcases h15443 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19993 (p7 p258 p686 p980 p1139 p1443 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h6761 : p1139)
    (h15444 : p7 ∨ (¬ p258) ∨ p686 ∨ (¬ p980) ∨ (¬ p1139) ∨ (¬ p1443) ∨ (¬ p1452)) : (¬ p258) ∨ (¬ p980) ∨ (¬ p1443) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p686) := by
    exact h16205
  have u6 : p1139 := by
    exact h6761
  rcases h15444 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19994 (p7 p101 p121 p686 p1135 p1325 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h6744 : p1135)
    (h15445 : p7 ∨ (¬ p101) ∨ (¬ p121) ∨ p686 ∨ (¬ p1135) ∨ (¬ p1325) ∨ (¬ p1452)) : (¬ p101) ∨ (¬ p121) ∨ (¬ p1325) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p686) := by
    exact h16205
  have u6 : p1135 := by
    exact h6744
  rcases h15445 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19995 (p6 p7 p156 p185 p192 p389 p657 p790 p833 p1206 : Prop)
    (h16152 : (¬ p7))
    (h15446 : (¬ p6) ∨ p7 ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p192) ∨ (¬ p389) ∨ (¬ p657) ∨ (¬ p790) ∨ (¬ p833) ∨ (¬ p1206)) : (¬ p6) ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p192) ∨ (¬ p389) ∨ (¬ p657) ∨ (¬ p790) ∨ (¬ p833) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
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
  have u5 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p833 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15446 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19996 (p7 p101 p121 p156 p185 p192 p206 p657 p686 p790 p833 p961 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h6744 : p1135)
    (h15447 : p7 ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p192) ∨ (¬ p206) ∨ (¬ p657) ∨ p686 ∨ (¬ p790) ∨ (¬ p833) ∨ (¬ p961) ∨ (¬ p1135)) : (¬ p101) ∨ (¬ p121) ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p192) ∨ (¬ p206) ∨ (¬ p657) ∨ (¬ p790) ∨ (¬ p833) ∨ (¬ p961) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p833 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : (¬ p686) := by
    exact h16205
  have u12 : p1135 := by
    exact h6744
  rcases h15447 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
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

theorem step19997 (p7 p9 p45 p193 p792 p864 p983 p1061 p1136 p1325 p1349 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16259 : (¬ p1136))
    (h15448 : p7 ∨ (¬ p9) ∨ (¬ p45) ∨ (¬ p193) ∨ (¬ p792) ∨ (¬ p864) ∨ (¬ p983) ∨ (¬ p1061) ∨ p1136 ∨ (¬ p1325) ∨ (¬ p1349)) : (¬ p9) ∨ (¬ p45) ∨ (¬ p193) ∨ (¬ p864) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1325) ∨ (¬ p1349) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1061 := by
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
  rcases h15448 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19998 (p6 p7 p8 p19 p64 p389 p657 p1100 p1141 p1208 : Prop)
    (h16152 : (¬ p7))
    (h15449 : (¬ p6) ∨ p7 ∨ (¬ p8) ∨ (¬ p19) ∨ (¬ p64) ∨ (¬ p389) ∨ (¬ p657) ∨ (¬ p1100) ∨ (¬ p1141) ∨ (¬ p1208)) : (¬ p6) ∨ (¬ p8) ∨ (¬ p19) ∨ (¬ p64) ∨ (¬ p389) ∨ (¬ p657) ∨ (¬ p1100) ∨ (¬ p1141) ∨ (¬ p1208) := by
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
  have u2 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1100 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1208 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15449 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19999 (p5 p6 p7 p389 p657 p904 p1096 p1206 : Prop)
    (h16152 : (¬ p7))
    (h15450 : (¬ p5) ∨ (¬ p6) ∨ p7 ∨ (¬ p389) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1206)) : (¬ p5) ∨ (¬ p6) ∨ (¬ p389) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1206) := by
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
  have u2 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p657 := by
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
  have u6 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15450 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20000 (p7 p45 p185 p193 p792 p925 p1035 p1060 p1074 p1226 p1484 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16345 : (¬ p1484))
    (h15451 : p7 ∨ (¬ p45) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p792) ∨ (¬ p925) ∨ (¬ p1035) ∨ (¬ p1060) ∨ (¬ p1074) ∨ (¬ p1226) ∨ p1484) : (¬ p45) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p925) ∨ (¬ p1035) ∨ (¬ p1060) ∨ (¬ p1074) ∨ (¬ p1226) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p925 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1060 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p792 := by
    exact h4535
  have u10 : (¬ p1484) := by
    exact h16345
  rcases h15451 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (u10 q10)

theorem step20002 (p6 p7 p45 p192 p595 p792 p1136 p1286 p1333 p1454 p1666 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16259 : (¬ p1136))
    (h15454 : (¬ p6) ∨ p7 ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p595) ∨ (¬ p792) ∨ p1136 ∨ (¬ p1286) ∨ (¬ p1333) ∨ (¬ p1454) ∨ (¬ p1666)) : (¬ p6) ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p595) ∨ (¬ p1286) ∨ (¬ p1333) ∨ (¬ p1454) ∨ (¬ p1666) := by
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
  have u2 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1454 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p792 := by
    exact h4535
  have u10 : (¬ p1136) := by
    exact h16259
  rcases h15454 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u9)
  · exact False.elim (u10 q6)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step20003 (p5 p6 p7 p101 p346 p738 p1096 p1562 : Prop)
    (h16152 : (¬ p7))
    (h15455 : (¬ p5) ∨ (¬ p6) ∨ p7 ∨ (¬ p101) ∨ (¬ p346) ∨ (¬ p738) ∨ (¬ p1096) ∨ (¬ p1562)) : (¬ p5) ∨ (¬ p6) ∨ (¬ p101) ∨ (¬ p346) ∨ (¬ p738) ∨ (¬ p1096) ∨ (¬ p1562) := by
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
  have u4 : p738 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15455 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20005 (p7 p160 p185 p193 p405 p669 p799 p816 p1115 p1325 : Prop)
    (h16152 : (¬ p7))
    (h15457 : p7 ∨ (¬ p160) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p405) ∨ (¬ p669) ∨ (¬ p799) ∨ (¬ p816) ∨ (¬ p1115) ∨ (¬ p1325)) : (¬ p160) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p405) ∨ (¬ p669) ∨ (¬ p799) ∨ (¬ p816) ∨ (¬ p1115) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p405 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p799 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15457 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step20006 (p7 p16 p167 p189 p225 p406 p620 p901 p1287 : Prop)
    (h16152 : (¬ p7))
    (h15458 : p7 ∨ (¬ p16) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p225) ∨ (¬ p406) ∨ (¬ p620) ∨ (¬ p901) ∨ (¬ p1287)) : (¬ p16) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p225) ∨ (¬ p406) ∨ (¬ p620) ∨ (¬ p901) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p620 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p901 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15458 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20007 (p7 p10 p134 p189 p279 p302 p303 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16285 : (¬ p302))
    (h15459 : p7 ∨ (¬ p10) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p279) ∨ p302 ∨ (¬ p303)) : (¬ p10) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p303) := by
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
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p279 := by
    exact h1444
  have u6 : (¬ p302) := by
    exact h16285
  rcases h15459 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step20008 (p7 p9 p16 p101 p134 p189 p343 p686 p904 p1061 p1074 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16205 : (¬ p686))
    (h15460 : p7 ∨ (¬ p9) ∨ (¬ p16) ∨ (¬ p101) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p343) ∨ p686 ∨ (¬ p904) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p9) ∨ (¬ p16) ∨ (¬ p101) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p904) ∨ (¬ p1061) ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p16 := by
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
  have u4 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p343 := by
    exact h1950
  have u10 : (¬ p686) := by
    exact h16205
  rcases h15460 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u9)
  · exact False.elim (u10 q7)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step20009 (p7 p88 p189 p419 p796 p924 p1099 p1229 p1291 : Prop)
    (h16152 : (¬ p7))
    (h15461 : p7 ∨ (¬ p88) ∨ (¬ p189) ∨ (¬ p419) ∨ (¬ p796) ∨ (¬ p924) ∨ (¬ p1099) ∨ (¬ p1229) ∨ (¬ p1291)) : (¬ p88) ∨ (¬ p189) ∨ (¬ p419) ∨ (¬ p796) ∨ (¬ p924) ∨ (¬ p1099) ∨ (¬ p1229) ∨ (¬ p1291) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1291 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15461 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20010 (p7 p101 p134 p189 p279 p1076 p1181 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16272 : (¬ p1181))
    (h15462 : p7 ∨ (¬ p101) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p279) ∨ (¬ p1076) ∨ p1181) : (¬ p101) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p279 := by
    exact h1444
  have u6 : (¬ p1181) := by
    exact h16272
  rcases h15462 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step20012 (p7 p125 p302 p419 p438 p681 p798 p1022 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h3892 : p681)
    (h15464 : p7 ∨ (¬ p125) ∨ p302 ∨ (¬ p419) ∨ (¬ p438) ∨ (¬ p681) ∨ (¬ p798) ∨ (¬ p1022)) : (¬ p125) ∨ (¬ p419) ∨ (¬ p438) ∨ (¬ p798) ∨ (¬ p1022) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p798 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p302) := by
    exact h16285
  have u7 : p681 := by
    exact h3892
  rcases h15464 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step20013 (p7 p134 p160 p161 p189 p279 p460 p686 p1057 p1077 p1206 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16205 : (¬ p686))
    (h15465 : p7 ∨ (¬ p134) ∨ (¬ p160) ∨ (¬ p161) ∨ (¬ p189) ∨ (¬ p279) ∨ (¬ p460) ∨ p686 ∨ (¬ p1057) ∨ (¬ p1077) ∨ (¬ p1206)) : (¬ p134) ∨ (¬ p160) ∨ (¬ p161) ∨ (¬ p189) ∨ (¬ p460) ∨ (¬ p1057) ∨ (¬ p1077) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p134 := by
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
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p460 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1057 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p279 := by
    exact h1444
  have u10 : (¬ p686) := by
    exact h16205
  rcases h15465 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u4)
  · exact False.elim (u10 q7)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step20014 (p7 p63 p924 p1055 p1095 p1097 : Prop)
    (h16152 : (¬ p7))
    (h15466 : p7 ∨ (¬ p63) ∨ (¬ p924) ∨ (¬ p1055) ∨ (¬ p1095) ∨ (¬ p1097)) : (¬ p63) ∨ (¬ p924) ∨ (¬ p1055) ∨ (¬ p1095) ∨ (¬ p1097) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1097 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15466 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20015 (p7 p63 p792 p1206 p1445 p1606 p1665 p1667 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16350 : (¬ p1445))
    (h15467 : p7 ∨ (¬ p63) ∨ (¬ p792) ∨ (¬ p1206) ∨ p1445 ∨ (¬ p1606) ∨ (¬ p1665) ∨ (¬ p1667)) : (¬ p63) ∨ (¬ p1206) ∨ (¬ p1606) ∨ (¬ p1665) ∨ (¬ p1667) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1606 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p792 := by
    exact h4535
  have u7 : (¬ p1445) := by
    exact h16350
  rcases h15467 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step20016 (p7 p157 p160 p189 p239 p419 p665 p796 p980 : Prop)
    (h16152 : (¬ p7))
    (h15468 : p7 ∨ (¬ p157) ∨ (¬ p160) ∨ (¬ p189) ∨ (¬ p239) ∨ (¬ p419) ∨ (¬ p665) ∨ (¬ p796) ∨ (¬ p980)) : (¬ p157) ∨ (¬ p160) ∨ (¬ p189) ∨ (¬ p239) ∨ (¬ p419) ∨ (¬ p665) ∨ (¬ p796) ∨ (¬ p980) := by
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
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p239 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15468 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20017 (p7 p88 p134 p189 p924 p983 p1061 p1098 p1454 p1666 : Prop)
    (h16152 : (¬ p7))
    (h15469 : p7 ∨ (¬ p88) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p924) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1098) ∨ (¬ p1454) ∨ (¬ p1666)) : (¬ p88) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p924) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1098) ∨ (¬ p1454) ∨ (¬ p1666) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1098 := by
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
  rcases h15469 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step20018 (p7 p88 p189 p435 p796 p924 p1232 p1311 p1547 p1674 : Prop)
    (h16152 : (¬ p7))
    (h15470 : p7 ∨ (¬ p88) ∨ (¬ p189) ∨ (¬ p435) ∨ (¬ p796) ∨ (¬ p924) ∨ (¬ p1232) ∨ (¬ p1311) ∨ (¬ p1547) ∨ (¬ p1674)) : (¬ p88) ∨ (¬ p189) ∨ (¬ p435) ∨ (¬ p796) ∨ (¬ p924) ∨ (¬ p1232) ∨ (¬ p1311) ∨ (¬ p1547) ∨ (¬ p1674) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1311 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1547 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1674 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15470 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step20019 (p7 p88 p134 p189 p362 p420 p498 p924 p1099 p1206 p1445 p1530 : Prop)
    (h16152 : (¬ p7))
    (h16350 : (¬ p1445))
    (h9352 : p1530)
    (h15471 : p7 ∨ (¬ p88) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p498) ∨ (¬ p924) ∨ (¬ p1099) ∨ (¬ p1206) ∨ p1445 ∨ (¬ p1530)) : (¬ p88) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p498) ∨ (¬ p924) ∨ (¬ p1099) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
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
  have u5 : p498 := by
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
  have u8 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p1445) := by
    exact h16350
  have u11 : p1530 := by
    exact h9352
  rcases h15471 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
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
  · exact False.elim (u10 q10)
  · exact False.elim (q11 u11)

theorem step20020 (p7 p63 p616 p924 p983 p1015 p1061 p1098 p1335 p1388 : Prop)
    (h16152 : (¬ p7))
    (h15472 : p7 ∨ (¬ p63) ∨ (¬ p616) ∨ (¬ p924) ∨ (¬ p983) ∨ (¬ p1015) ∨ (¬ p1061) ∨ (¬ p1098) ∨ (¬ p1335) ∨ (¬ p1388)) : (¬ p63) ∨ (¬ p616) ∨ (¬ p924) ∨ (¬ p983) ∨ (¬ p1015) ∨ (¬ p1061) ∨ (¬ p1098) ∨ (¬ p1335) ∨ (¬ p1388) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1098 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1388 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15472 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step20022 (p7 p63 p301 p302 p303 p495 p574 p792 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h4535 : p792)
    (h15474 : p7 ∨ (¬ p63) ∨ (¬ p301) ∨ p302 ∨ (¬ p303) ∨ (¬ p495) ∨ (¬ p574) ∨ (¬ p792)) : (¬ p63) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p495) ∨ (¬ p574) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p574 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p302) := by
    exact h16285
  have u7 : p792 := by
    exact h4535
  rcases h15474 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step20024 (p7 p156 p185 p406 p797 p820 p858 : Prop)
    (h16152 : (¬ p7))
    (h15476 : p7 ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p406) ∨ (¬ p797) ∨ (¬ p820) ∨ (¬ p858)) : (¬ p156) ∨ (¬ p185) ∨ (¬ p406) ∨ (¬ p797) ∨ (¬ p820) ∨ (¬ p858) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p797 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p820 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15476 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20025 (p7 p101 p121 p160 p686 p960 p980 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h6761 : p1139)
    (h15477 : p7 ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p160) ∨ p686 ∨ (¬ p960) ∨ (¬ p980) ∨ (¬ p1139)) : (¬ p101) ∨ (¬ p121) ∨ (¬ p160) ∨ (¬ p960) ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p960 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p686) := by
    exact h16205
  have u7 : p1139 := by
    exact h6761
  rcases h15477 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step20026 (p7 p11 p13 p17 p156 p193 p923 p980 p1225 p1311 : Prop)
    (h16152 : (¬ p7))
    (h15478 : p7 ∨ (¬ p11) ∨ (¬ p13) ∨ (¬ p17) ∨ (¬ p156) ∨ (¬ p193) ∨ (¬ p923) ∨ (¬ p980) ∨ (¬ p1225) ∨ (¬ p1311)) : (¬ p11) ∨ (¬ p13) ∨ (¬ p17) ∨ (¬ p156) ∨ (¬ p193) ∨ (¬ p923) ∨ (¬ p980) ∨ (¬ p1225) ∨ (¬ p1311) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p923 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1311 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15478 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step20027 (p7 p69 p280 p387 p419 p1184 p1187 : Prop)
    (h16152 : (¬ p7))
    (h16173 : (¬ p280))
    (h7053 : p1184)
    (h15479 : p7 ∨ (¬ p69) ∨ p280 ∨ (¬ p387) ∨ (¬ p419) ∨ (¬ p1184) ∨ (¬ p1187)) : (¬ p69) ∨ (¬ p387) ∨ (¬ p419) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
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
  have u6 : p1184 := by
    exact h7053
  rcases h15479 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step20028 (p2 p7 p156 p185 p192 p387 p419 p517 p790 : Prop)
    (h16152 : (¬ p7))
    (h15480 : (¬ p2) ∨ p7 ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p192) ∨ (¬ p387) ∨ (¬ p419) ∨ (¬ p517) ∨ (¬ p790)) : (¬ p2) ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p192) ∨ (¬ p387) ∨ (¬ p419) ∨ (¬ p517) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p517 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15480 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20029 (p6 p7 p19 p48 p156 p192 p918 : Prop)
    (h16152 : (¬ p7))
    (h15481 : (¬ p6) ∨ p7 ∨ (¬ p19) ∨ (¬ p48) ∨ (¬ p156) ∨ (¬ p192) ∨ (¬ p918)) : (¬ p6) ∨ (¬ p19) ∨ (¬ p48) ∨ (¬ p156) ∨ (¬ p192) ∨ (¬ p918) := by
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
  have u2 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15481 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20030 (p7 p42 p193 p280 p387 p419 p798 p814 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16173 : (¬ p280))
    (h15483 : p7 ∨ (¬ p42) ∨ (¬ p193) ∨ p280 ∨ (¬ p387) ∨ (¬ p419) ∨ (¬ p798) ∨ (¬ p814)) : (¬ p193) ∨ (¬ p387) ∨ (¬ p419) ∨ (¬ p798) ∨ (¬ p814) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
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
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p280) := by
    exact h16173
  rcases h15483 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (u7 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step20032 (p7 p9 p101 p125 p323 p500 p638 p1061 p1074 : Prop)
    (h16152 : (¬ p7))
    (h15485 : p7 ∨ (¬ p9) ∨ (¬ p101) ∨ (¬ p125) ∨ (¬ p323) ∨ (¬ p500) ∨ (¬ p638) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p9) ∨ (¬ p101) ∨ (¬ p125) ∨ (¬ p323) ∨ (¬ p500) ∨ (¬ p638) ∨ (¬ p1061) ∨ (¬ p1074) := by
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
  have u3 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p638 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15485 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20033 (p7 p668 p897 p1099 p1229 p1310 : Prop)
    (h16152 : (¬ p7))
    (h15486 : p7 ∨ (¬ p668) ∨ (¬ p897) ∨ (¬ p1099) ∨ (¬ p1229) ∨ (¬ p1310)) : (¬ p668) ∨ (¬ p897) ∨ (¬ p1099) ∨ (¬ p1229) ∨ (¬ p1310) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p897 := by
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
  rcases h15486 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20034 (p7 p16 p17 p258 p346 p738 p1096 p1562 : Prop)
    (h16152 : (¬ p7))
    (h15488 : p7 ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p258) ∨ (¬ p346) ∨ (¬ p738) ∨ (¬ p1096) ∨ (¬ p1562)) : (¬ p16) ∨ (¬ p17) ∨ (¬ p258) ∨ (¬ p346) ∨ (¬ p738) ∨ (¬ p1096) ∨ (¬ p1562) := by
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
  have u4 : p738 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15488 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20035 (p302 p326 p419 p788 : Prop)
    (h16285 : (¬ p302))
    (h5066 : p788)
    (h15489 : p302 ∨ p326 ∨ (¬ p419) ∨ (¬ p788)) : p326 ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p326) := fun hu => hn (Or.inl hu)
  have u1 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p302) := by
    exact h16285
  have u3 : p788 := by
    exact h5066
  rcases h15489 with q0 | q1 | q2 | q3
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)

theorem step20036 (p7 p126 p258 p308 p348 p710 : Prop)
    (h16152 : (¬ p7))
    (h15490 : p7 ∨ (¬ p126) ∨ (¬ p258) ∨ (¬ p308) ∨ (¬ p348) ∨ (¬ p710)) : (¬ p126) ∨ (¬ p258) ∨ (¬ p308) ∨ (¬ p348) ∨ (¬ p710) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p126 := by
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
  have u3 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15490 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20037 (p7 p90 p106 p163 p193 p241 p344 p710 p918 : Prop)
    (h16152 : (¬ p7))
    (h15491 : p7 ∨ (¬ p90) ∨ (¬ p106) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p241) ∨ (¬ p344) ∨ (¬ p710) ∨ (¬ p918)) : (¬ p90) ∨ (¬ p106) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p241) ∨ (¬ p344) ∨ (¬ p710) ∨ (¬ p918) := by
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
  have u4 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15491 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20038 (p7 p265 p305 p344 p576 p710 p792 p1076 p1181 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16272 : (¬ p1181))
    (h15492 : p7 ∨ (¬ p265) ∨ (¬ p305) ∨ (¬ p344) ∨ (¬ p576) ∨ (¬ p710) ∨ (¬ p792) ∨ (¬ p1076) ∨ p1181) : (¬ p265) ∨ (¬ p305) ∨ (¬ p344) ∨ (¬ p576) ∨ (¬ p710) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : p792 := by
    exact h4535
  have u8 : (¬ p1181) := by
    exact h16272
  rcases h15492 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u5)
  · exact False.elim (u8 q8)

theorem step20039 (p7 p132 p185 p256 p302 p303 p348 p836 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16285 : (¬ p302))
    (h15493 : p7 ∨ (¬ p132) ∨ (¬ p185) ∨ (¬ p256) ∨ p302 ∨ (¬ p303) ∨ (¬ p348) ∨ (¬ p836)) : (¬ p185) ∨ (¬ p256) ∨ (¬ p303) ∨ (¬ p348) ∨ (¬ p836) := by
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
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p132 := by
    exact h786
  have u7 : (¬ p302) := by
    exact h16285
  rcases h15493 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step20040 (p7 p135 p170 p238 p256 p710 p840 : Prop)
    (h16152 : (¬ p7))
    (h15494 : p7 ∨ (¬ p135) ∨ (¬ p170) ∨ (¬ p238) ∨ (¬ p256) ∨ (¬ p710) ∨ (¬ p840)) : (¬ p135) ∨ (¬ p170) ∨ (¬ p238) ∨ (¬ p256) ∨ (¬ p710) ∨ (¬ p840) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15494 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20041 (p7 p265 p302 p305 p576 p792 p980 p1055 p1333 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h4535 : p792)
    (h15495 : p7 ∨ (¬ p265) ∨ p302 ∨ (¬ p305) ∨ (¬ p576) ∨ (¬ p792) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1333)) : (¬ p265) ∨ (¬ p305) ∨ (¬ p576) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p576 := by
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
  have u5 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p302) := by
    exact h16285
  have u8 : p792 := by
    exact h4535
  rcases h15495 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step20042 (p7 p43 p135 p283 p928 p1710 p1713 : Prop)
    (h16152 : (¬ p7))
    (h15496 : p7 ∨ (¬ p43) ∨ (¬ p135) ∨ (¬ p283) ∨ (¬ p928) ∨ (¬ p1710) ∨ (¬ p1713)) : (¬ p43) ∨ (¬ p135) ∨ (¬ p283) ∨ (¬ p928) ∨ (¬ p1710) ∨ (¬ p1713) := by
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
  have u2 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1713 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15496 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20043 (p7 p88 p140 p189 p283 p928 p1689 p1711 : Prop)
    (h16152 : (¬ p7))
    (h15497 : p7 ∨ (¬ p88) ∨ (¬ p140) ∨ (¬ p189) ∨ (¬ p283) ∨ (¬ p928) ∨ (¬ p1689) ∨ (¬ p1711)) : (¬ p88) ∨ (¬ p140) ∨ (¬ p189) ∨ (¬ p283) ∨ (¬ p928) ∨ (¬ p1689) ∨ (¬ p1711) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1689 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1711 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15497 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20044 (p7 p15 p303 p305 p348 p500 p710 p1325 p1469 p1712 : Prop)
    (h16152 : (¬ p7))
    (h15498 : p7 ∨ (¬ p15) ∨ (¬ p303) ∨ (¬ p305) ∨ (¬ p348) ∨ (¬ p500) ∨ (¬ p710) ∨ (¬ p1325) ∨ (¬ p1469) ∨ (¬ p1712)) : (¬ p15) ∨ (¬ p303) ∨ (¬ p305) ∨ (¬ p348) ∨ (¬ p500) ∨ (¬ p710) ∨ (¬ p1325) ∨ (¬ p1469) ∨ (¬ p1712) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1469 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1712 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15498 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step20045 (p7 p106 p169 p237 p1077 p1118 p1349 : Prop)
    (h16152 : (¬ p7))
    (h15499 : p7 ∨ (¬ p106) ∨ (¬ p169) ∨ (¬ p237) ∨ (¬ p1077) ∨ (¬ p1118) ∨ (¬ p1349)) : (¬ p106) ∨ (¬ p169) ∨ (¬ p237) ∨ (¬ p1077) ∨ (¬ p1118) ∨ (¬ p1349) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p169 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1118 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15499 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20046 (p7 p135 p189 p305 p425 p579 p860 p980 p1055 p1333 p1346 : Prop)
    (h16152 : (¬ p7))
    (h15500 : p7 ∨ (¬ p135) ∨ (¬ p189) ∨ (¬ p305) ∨ (¬ p425) ∨ (¬ p579) ∨ (¬ p860) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1333) ∨ (¬ p1346)) : (¬ p135) ∨ (¬ p189) ∨ (¬ p305) ∨ (¬ p425) ∨ (¬ p579) ∨ (¬ p860) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1333) ∨ (¬ p1346) := by
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
  have u2 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p860 := by
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
  have u8 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h15500 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step20047 (p7 p15 p125 p234 p303 p500 p1334 p1366 : Prop)
    (h16152 : (¬ p7))
    (h15501 : p7 ∨ (¬ p15) ∨ (¬ p125) ∨ (¬ p234) ∨ (¬ p303) ∨ (¬ p500) ∨ (¬ p1334) ∨ (¬ p1366)) : (¬ p15) ∨ (¬ p125) ∨ (¬ p234) ∨ (¬ p303) ∨ (¬ p500) ∨ (¬ p1334) ∨ (¬ p1366) := by
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
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15501 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20048 (p7 p106 p135 p189 p265 p305 p344 p435 p539 p687 p710 p820 : Prop)
    (h16152 : (¬ p7))
    (h15502 : p7 ∨ (¬ p106) ∨ (¬ p135) ∨ (¬ p189) ∨ (¬ p265) ∨ (¬ p305) ∨ (¬ p344) ∨ (¬ p435) ∨ (¬ p539) ∨ (¬ p687) ∨ (¬ p710) ∨ (¬ p820)) : (¬ p106) ∨ (¬ p135) ∨ (¬ p189) ∨ (¬ p265) ∨ (¬ p305) ∨ (¬ p344) ∨ (¬ p435) ∨ (¬ p539) ∨ (¬ p687) ∨ (¬ p710) ∨ (¬ p820) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p539 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p820 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : (¬ p7) := by
    exact h16152
  rcases h15502 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
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

theorem step20050 (p7 p129 p164 p189 p225 p237 p840 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h789 : p164)
    (h15505 : p7 ∨ p129 ∨ (¬ p164) ∨ (¬ p189) ∨ (¬ p225) ∨ (¬ p237) ∨ (¬ p840)) : (¬ p189) ∨ (¬ p225) ∨ (¬ p237) ∨ (¬ p840) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p164 := by
    exact h789
  rcases h15505 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step20052 (p7 p45 p135 p265 p305 p710 p904 p927 : Prop)
    (h16152 : (¬ p7))
    (h15507 : p7 ∨ (¬ p45) ∨ (¬ p135) ∨ (¬ p265) ∨ (¬ p305) ∨ (¬ p710) ∨ (¬ p904) ∨ (¬ p927)) : (¬ p45) ∨ (¬ p135) ∨ (¬ p265) ∨ (¬ p305) ∨ (¬ p710) ∨ (¬ p904) ∨ (¬ p927) := by
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
  have u3 : p305 := by
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
  have u6 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15507 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20053 (p7 p43 p135 p283 p834 p1141 p1256 p1393 : Prop)
    (h16152 : (¬ p7))
    (h15508 : p7 ∨ (¬ p43) ∨ (¬ p135) ∨ (¬ p283) ∨ (¬ p834) ∨ (¬ p1141) ∨ (¬ p1256) ∨ (¬ p1393)) : (¬ p43) ∨ (¬ p135) ∨ (¬ p283) ∨ (¬ p834) ∨ (¬ p1141) ∨ (¬ p1256) ∨ (¬ p1393) := by
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
  have u2 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p834 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15508 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20055 (p7 p264 p288 p305 p344 p710 : Prop)
    (h16152 : (¬ p7))
    (h15510 : p7 ∨ (¬ p264) ∨ (¬ p288) ∨ (¬ p305) ∨ (¬ p344) ∨ (¬ p710)) : (¬ p264) ∨ (¬ p288) ∨ (¬ p305) ∨ (¬ p344) ∨ (¬ p710) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p264 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p305 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15510 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20056 (p7 p19 p229 p344 p560 p686 p710 p788 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h5066 : p788)
    (h15512 : p7 ∨ (¬ p19) ∨ (¬ p229) ∨ (¬ p344) ∨ (¬ p560) ∨ p686 ∨ (¬ p710) ∨ (¬ p788)) : (¬ p19) ∨ (¬ p229) ∨ (¬ p344) ∨ (¬ p560) ∨ (¬ p710) := by
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
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p686) := by
    exact h16205
  have u7 : p788 := by
    exact h5066
  rcases h15512 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step20057 (p7 p63 p69 p129 p792 p1141 p1256 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h4535 : p792)
    (h15513 : p7 ∨ (¬ p63) ∨ (¬ p69) ∨ p129 ∨ (¬ p792) ∨ (¬ p1141) ∨ (¬ p1256)) : (¬ p63) ∨ (¬ p69) ∨ (¬ p1141) ∨ (¬ p1256) := by
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
  have u2 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p792 := by
    exact h4535
  rcases h15513 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step20058 (p7 p185 p279 p344 p836 p1076 p1181 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16272 : (¬ p1181))
    (h15514 : p7 ∨ (¬ p185) ∨ (¬ p279) ∨ (¬ p344) ∨ (¬ p836) ∨ (¬ p1076) ∨ p1181) : (¬ p185) ∨ (¬ p344) ∨ (¬ p836) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
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
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p279 := by
    exact h1444
  have u6 : (¬ p1181) := by
    exact h16272
  rcases h15514 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step20059 (p7 p17 p39 p88 p301 p423 p438 p1035 p1335 : Prop)
    (h16152 : (¬ p7))
    (h15515 : p7 ∨ (¬ p17) ∨ (¬ p39) ∨ (¬ p88) ∨ (¬ p301) ∨ (¬ p423) ∨ (¬ p438) ∨ (¬ p1035) ∨ (¬ p1335)) : (¬ p17) ∨ (¬ p39) ∨ (¬ p88) ∨ (¬ p301) ∨ (¬ p423) ∨ (¬ p438) ∨ (¬ p1035) ∨ (¬ p1335) := by
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
  have u2 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15515 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20060 (p7 p261 p279 p305 p344 p710 p980 p1076 p1324 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16309 : (¬ p1324))
    (h15516 : p7 ∨ (¬ p261) ∨ (¬ p279) ∨ (¬ p305) ∨ (¬ p344) ∨ (¬ p710) ∨ (¬ p980) ∨ (¬ p1076) ∨ p1324) : (¬ p261) ∨ (¬ p305) ∨ (¬ p344) ∨ (¬ p710) ∨ (¬ p980) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p305 := by
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
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : p279 := by
    exact h1444
  have u8 : (¬ p1324) := by
    exact h16309
  rcases h15516 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u8 q8)

theorem step20061 (p7 p17 p160 p258 p1040 p1076 p1350 p1465 : Prop)
    (h16152 : (¬ p7))
    (h15517 : p7 ∨ (¬ p17) ∨ (¬ p160) ∨ (¬ p258) ∨ (¬ p1040) ∨ (¬ p1076) ∨ (¬ p1350) ∨ (¬ p1465)) : (¬ p17) ∨ (¬ p160) ∨ (¬ p258) ∨ (¬ p1040) ∨ (¬ p1076) ∨ (¬ p1350) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1040 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15517 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20062 (p7 p170 p210 p305 p422 p710 p840 p1209 : Prop)
    (h16152 : (¬ p7))
    (h15518 : p7 ∨ (¬ p170) ∨ (¬ p210) ∨ (¬ p305) ∨ (¬ p422) ∨ (¬ p710) ∨ (¬ p840) ∨ (¬ p1209)) : (¬ p170) ∨ (¬ p210) ∨ (¬ p305) ∨ (¬ p422) ∨ (¬ p710) ∨ (¬ p840) ∨ (¬ p1209) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15518 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20063 (p7 p14 p71 p164 p305 p344 p500 p710 p1076 p1140 p1141 p1181 : Prop)
    (h16152 : (¬ p7))
    (h789 : p164)
    (h16272 : (¬ p1181))
    (h15519 : p7 ∨ (¬ p14) ∨ (¬ p71) ∨ (¬ p164) ∨ (¬ p305) ∨ (¬ p344) ∨ (¬ p500) ∨ (¬ p710) ∨ (¬ p1076) ∨ (¬ p1140) ∨ (¬ p1141) ∨ p1181) : (¬ p14) ∨ (¬ p71) ∨ (¬ p305) ∨ (¬ p344) ∨ (¬ p500) ∨ (¬ p710) ∨ (¬ p1076) ∨ (¬ p1140) ∨ (¬ p1141) := by
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
  have u2 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p164 := by
    exact h789
  have u11 : (¬ p1181) := by
    exact h16272
  rcases h15519 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u8)
  · exact False.elim (u11 q11)

theorem step20064 (p7 p17 p39 p69 p88 p258 p1076 p1181 p1225 p1229 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16272 : (¬ p1181))
    (h8348 : p1386)
    (h15520 : p7 ∨ (¬ p17) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p258) ∨ (¬ p1076) ∨ p1181 ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1386)) : (¬ p17) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p258) ∨ (¬ p1076) ∨ (¬ p1225) ∨ (¬ p1229) := by
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
  have u5 : p1076 := by
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
  have u9 : (¬ p1181) := by
    exact h16272
  have u10 : p1386 := by
    exact h8348
  rcases h15520 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step20065 (p7 p14 p106 p1038 p1077 p1141 : Prop)
    (h16152 : (¬ p7))
    (h15521 : p7 ∨ (¬ p14) ∨ (¬ p106) ∨ (¬ p1038) ∨ (¬ p1077) ∨ (¬ p1141)) : (¬ p14) ∨ (¬ p106) ∨ (¬ p1038) ∨ (¬ p1077) ∨ (¬ p1141) := by
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
  have u2 : p1038 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15521 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20066 (p7 p14 p15 p16 p106 p125 p126 p258 p261 : Prop)
    (h16152 : (¬ p7))
    (h15522 : p7 ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p106) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p258) ∨ (¬ p261)) : (¬ p14) ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p106) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p258) ∨ (¬ p261) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
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
  have u3 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15522 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20067 (p7 p17 p39 p69 p88 p301 p303 p1000 p1145 p1229 : Prop)
    (h16152 : (¬ p7))
    (h15523 : p7 ∨ (¬ p17) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p1000) ∨ (¬ p1145) ∨ (¬ p1229)) : (¬ p17) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p1000) ∨ (¬ p1145) ∨ (¬ p1229) := by
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
  have u4 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1145 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15523 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step20068 (p7 p39 p69 p88 p106 p185 p344 p836 p883 p1096 : Prop)
    (h16152 : (¬ p7))
    (h15524 : p7 ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p106) ∨ (¬ p185) ∨ (¬ p344) ∨ (¬ p836) ∨ (¬ p883) ∨ (¬ p1096)) : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p106) ∨ (¬ p185) ∨ (¬ p344) ∨ (¬ p836) ∨ (¬ p883) ∨ (¬ p1096) := by
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
  have u3 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15524 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step20069 (p7 p17 p83 p430 p581 p1015 p1184 p1385 : Prop)
    (h16152 : (¬ p7))
    (h16180 : (¬ p430))
    (h7053 : p1184)
    (h15525 : p7 ∨ (¬ p17) ∨ (¬ p83) ∨ p430 ∨ (¬ p581) ∨ (¬ p1015) ∨ (¬ p1184) ∨ (¬ p1385)) : (¬ p17) ∨ (¬ p83) ∨ (¬ p581) ∨ (¬ p1015) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p430) := by
    exact h16180
  have u7 : p1184 := by
    exact h7053
  rcases h15525 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step20071 (p7 p45 p129 p160 p420 p438 p495 p1184 p1273 p1335 p1348 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h7053 : p1184)
    (h15527 : p7 ∨ (¬ p45) ∨ p129 ∨ (¬ p160) ∨ (¬ p420) ∨ (¬ p438) ∨ (¬ p495) ∨ (¬ p1184) ∨ (¬ p1273) ∨ (¬ p1335) ∨ (¬ p1348)) : (¬ p45) ∨ (¬ p160) ∨ (¬ p420) ∨ (¬ p438) ∨ (¬ p495) ∨ (¬ p1273) ∨ (¬ p1335) ∨ (¬ p1348) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p129) := by
    exact h16154
  have u10 : p1184 := by
    exact h7053
  rcases h15527 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u9 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step20072 (p7 p17 p279 p302 p303 p515 p581 p1385 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16285 : (¬ p302))
    (h15528 : p7 ∨ (¬ p17) ∨ (¬ p279) ∨ p302 ∨ (¬ p303) ∨ (¬ p515) ∨ (¬ p581) ∨ (¬ p1385)) : (¬ p17) ∨ (¬ p303) ∨ (¬ p515) ∨ (¬ p581) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p515 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p279 := by
    exact h1444
  have u7 : (¬ p302) := by
    exact h16285
  rcases h15528 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (u7 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step20073 (p7 p17 p83 p581 p686 p1077 p1118 p1184 p1249 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h7053 : p1184)
    (h15529 : p7 ∨ (¬ p17) ∨ (¬ p83) ∨ (¬ p581) ∨ p686 ∨ (¬ p1077) ∨ (¬ p1118) ∨ (¬ p1184) ∨ (¬ p1249)) : (¬ p17) ∨ (¬ p83) ∨ (¬ p581) ∨ (¬ p1077) ∨ (¬ p1118) ∨ (¬ p1249) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1118 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p686) := by
    exact h16205
  have u8 : p1184 := by
    exact h7053
  rcases h15529 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u5)

theorem step20074 (p7 p265 p304 p576 p792 p980 p1076 p1324 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16309 : (¬ p1324))
    (h15532 : p7 ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p576) ∨ (¬ p792) ∨ (¬ p980) ∨ (¬ p1076) ∨ p1324) : (¬ p265) ∨ (¬ p304) ∨ (¬ p576) ∨ (¬ p980) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p576 := by
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
  have u6 : p792 := by
    exact h4535
  have u7 : (¬ p1324) := by
    exact h16309
  rcases h15532 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step20075 (p7 p15 p305 p346 p423 p426 p500 p756 p769 p1035 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h8348 : p1386)
    (h15533 : p7 ∨ (¬ p15) ∨ (¬ p305) ∨ (¬ p346) ∨ (¬ p423) ∨ p426 ∨ (¬ p500) ∨ (¬ p756) ∨ (¬ p769) ∨ (¬ p1035) ∨ (¬ p1386)) : (¬ p15) ∨ (¬ p305) ∨ (¬ p346) ∨ (¬ p423) ∨ (¬ p500) ∨ (¬ p756) ∨ (¬ p769) ∨ (¬ p1035) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p426) := by
    exact h16178
  have u10 : p1386 := by
    exact h8348
  rcases h15533 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u9 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u10)

theorem step20076 (p7 p15 p304 p500 p980 p1076 p1469 p1712 : Prop)
    (h16152 : (¬ p7))
    (h15534 : p7 ∨ (¬ p15) ∨ (¬ p304) ∨ (¬ p500) ∨ (¬ p980) ∨ (¬ p1076) ∨ (¬ p1469) ∨ (¬ p1712)) : (¬ p15) ∨ (¬ p304) ∨ (¬ p500) ∨ (¬ p980) ∨ (¬ p1076) ∨ (¬ p1469) ∨ (¬ p1712) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
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
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1469 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1712 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15534 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20078 (p7 p41 p189 p230 p1035 p1255 p1346 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h8348 : p1386)
    (h15536 : p7 ∨ (¬ p41) ∨ (¬ p189) ∨ p230 ∨ (¬ p1035) ∨ (¬ p1255) ∨ (¬ p1346) ∨ (¬ p1386)) : (¬ p41) ∨ (¬ p189) ∨ (¬ p1035) ∨ (¬ p1255) ∨ (¬ p1346) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1035 := by
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
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p1386 := by
    exact h8348
  rcases h15536 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step20079 (p7 p45 p84 p135 p265 p305 p346 p426 p756 p769 p1035 p1255 p1346 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h8348 : p1386)
    (h15537 : p7 ∨ (¬ p45) ∨ (¬ p84) ∨ (¬ p135) ∨ (¬ p265) ∨ (¬ p305) ∨ (¬ p346) ∨ p426 ∨ (¬ p756) ∨ (¬ p769) ∨ (¬ p1035) ∨ (¬ p1255) ∨ (¬ p1346) ∨ (¬ p1386)) : (¬ p45) ∨ (¬ p84) ∨ (¬ p135) ∨ (¬ p265) ∨ (¬ p305) ∨ (¬ p346) ∨ (¬ p756) ∨ (¬ p769) ∨ (¬ p1035) ∨ (¬ p1255) ∨ (¬ p1346) := by
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
  have u4 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : (¬ p7) := by
    exact h16152
  have u12 : (¬ p426) := by
    exact h16178
  have u13 : p1386 := by
    exact h8348
  rcases h15537 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13
  · exact False.elim (u11 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u12 q7)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u8)
  · exact False.elim (q11 u9)
  · exact False.elim (q12 u10)
  · exact False.elim (q13 u13)

theorem step20080 (p7 p70 p495 p636 p726 p985 p1035 p1140 : Prop)
    (h16152 : (¬ p7))
    (h15538 : p7 ∨ (¬ p70) ∨ (¬ p495) ∨ (¬ p636) ∨ (¬ p726) ∨ (¬ p985) ∨ (¬ p1035) ∨ (¬ p1140)) : (¬ p70) ∨ (¬ p495) ∨ (¬ p636) ∨ (¬ p726) ∨ (¬ p985) ∨ (¬ p1035) ∨ (¬ p1140) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p70 := by
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
  have u3 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15538 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20081 (p7 p135 p234 p265 p304 p346 p542 p1141 p1256 : Prop)
    (h16152 : (¬ p7))
    (h15539 : p7 ∨ (¬ p135) ∨ (¬ p234) ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p542) ∨ (¬ p1141) ∨ (¬ p1256)) : (¬ p135) ∨ (¬ p234) ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p542) ∨ (¬ p1141) ∨ (¬ p1256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p234 := by
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
  have u4 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15539 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20082 (p7 p303 p420 p426 p495 p657 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h7053 : p1184)
    (h15540 : p7 ∨ (¬ p303) ∨ (¬ p420) ∨ p426 ∨ (¬ p495) ∨ (¬ p657) ∨ (¬ p1184)) : (¬ p303) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p657) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p303 := by
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
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p426) := by
    exact h16178
  have u6 : p1184 := by
    exact h7053
  rcases h15540 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step20083 (p7 p43 p135 p187 p481 p581 p1187 : Prop)
    (h16152 : (¬ p7))
    (h15541 : p7 ∨ (¬ p43) ∨ (¬ p135) ∨ (¬ p187) ∨ (¬ p481) ∨ (¬ p581) ∨ (¬ p1187)) : (¬ p43) ∨ (¬ p135) ∨ (¬ p187) ∨ (¬ p481) ∨ (¬ p581) ∨ (¬ p1187) := by
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
  have u2 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15541 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20084 (p7 p41 p189 p230 p304 p420 p494 p517 p633 p790 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h7053 : p1184)
    (h15542 : p7 ∨ (¬ p41) ∨ (¬ p189) ∨ p230 ∨ (¬ p304) ∨ (¬ p420) ∨ (¬ p494) ∨ (¬ p517) ∨ (¬ p633) ∨ (¬ p790) ∨ (¬ p1184)) : (¬ p41) ∨ (¬ p189) ∨ (¬ p304) ∨ (¬ p420) ∨ (¬ p494) ∨ (¬ p517) ∨ (¬ p633) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p517 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p230) := by
    exact h16165
  have u10 : p1184 := by
    exact h7053
  rcases h15542 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u9 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u10)

theorem step20085 (p7 p41 p189 p230 p685 p790 p801 p1366 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h3898 : p685)
    (h15543 : p7 ∨ (¬ p41) ∨ (¬ p189) ∨ p230 ∨ (¬ p685) ∨ (¬ p790) ∨ (¬ p801) ∨ (¬ p1366)) : (¬ p41) ∨ (¬ p189) ∨ (¬ p790) ∨ (¬ p801) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p801 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p685 := by
    exact h3898
  rcases h15543 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step20086 (p7 p41 p189 p224 p230 p304 p639 p681 p860 p897 p1346 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h3892 : p681)
    (h15544 : p7 ∨ (¬ p41) ∨ (¬ p189) ∨ (¬ p224) ∨ p230 ∨ (¬ p304) ∨ (¬ p639) ∨ (¬ p681) ∨ (¬ p860) ∨ (¬ p897) ∨ (¬ p1346)) : (¬ p41) ∨ (¬ p189) ∨ (¬ p224) ∨ (¬ p304) ∨ (¬ p639) ∨ (¬ p860) ∨ (¬ p897) ∨ (¬ p1346) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p639 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p860 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p230) := by
    exact h16165
  have u10 : p681 := by
    exact h3892
  rcases h15544 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u9 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step20087 (p7 p41 p160 p224 p230 p304 p639 p681 p897 p1000 p1250 p1348 p1465 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h3892 : p681)
    (h15545 : p7 ∨ (¬ p41) ∨ (¬ p160) ∨ (¬ p224) ∨ p230 ∨ (¬ p304) ∨ (¬ p639) ∨ (¬ p681) ∨ (¬ p897) ∨ (¬ p1000) ∨ (¬ p1250) ∨ (¬ p1348) ∨ (¬ p1465)) : (¬ p41) ∨ (¬ p160) ∨ (¬ p224) ∨ (¬ p304) ∨ (¬ p639) ∨ (¬ p897) ∨ (¬ p1000) ∨ (¬ p1250) ∨ (¬ p1348) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p639 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1250 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : (¬ p230) := by
    exact h16165
  have u12 : p681 := by
    exact h3892
  rcases h15545 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u11 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u12)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)
  · exact False.elim (q12 u9)

theorem step20088 (p7 p15 p125 p234 p303 p500 p542 p657 : Prop)
    (h16152 : (¬ p7))
    (h15546 : p7 ∨ (¬ p15) ∨ (¬ p125) ∨ (¬ p234) ∨ (¬ p303) ∨ (¬ p500) ∨ (¬ p542) ∨ (¬ p657)) : (¬ p15) ∨ (¬ p125) ∨ (¬ p234) ∨ (¬ p303) ∨ (¬ p500) ∨ (¬ p542) ∨ (¬ p657) := by
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
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p500 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15546 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20089 (p7 p15 p224 p304 p346 p423 p500 p1000 : Prop)
    (h16152 : (¬ p7))
    (h15547 : p7 ∨ (¬ p15) ∨ (¬ p224) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p423) ∨ (¬ p500) ∨ (¬ p1000)) : (¬ p15) ∨ (¬ p224) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p423) ∨ (¬ p500) ∨ (¬ p1000) := by
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
  have u2 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p346 := by
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
  have u6 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15547 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20092 (p7 p16 p19 p71 p185 p224 p302 p788 p836 p1140 p1141 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h5066 : p788)
    (h15550 : p7 ∨ (¬ p16) ∨ (¬ p19) ∨ (¬ p71) ∨ (¬ p185) ∨ (¬ p224) ∨ p302 ∨ (¬ p788) ∨ (¬ p836) ∨ (¬ p1140) ∨ (¬ p1141)) : (¬ p16) ∨ (¬ p19) ∨ (¬ p71) ∨ (¬ p185) ∨ (¬ p224) ∨ (¬ p836) ∨ (¬ p1140) ∨ (¬ p1141) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p302) := by
    exact h16285
  have u10 : p788 := by
    exact h5066
  rcases h15550 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u9 q6)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step20094 (p7 p19 p382 p426 p480 p657 p788 p1187 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h5066 : p788)
    (h15552 : p7 ∨ (¬ p19) ∨ (¬ p382) ∨ p426 ∨ (¬ p480) ∨ (¬ p657) ∨ (¬ p788) ∨ (¬ p1187)) : (¬ p19) ∨ (¬ p382) ∨ (¬ p480) ∨ (¬ p657) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p480 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p426) := by
    exact h16178
  have u7 : p788 := by
    exact h5066
  rcases h15552 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step20095 (p7 p101 p143 p287 p309 p710 p840 : Prop)
    (h16152 : (¬ p7))
    (h15553 : p7 ∨ (¬ p101) ∨ (¬ p143) ∨ (¬ p287) ∨ (¬ p309) ∨ (¬ p710) ∨ (¬ p840)) : (¬ p101) ∨ (¬ p143) ∨ (¬ p287) ∨ (¬ p309) ∨ (¬ p710) ∨ (¬ p840) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15553 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20096 (p7 p101 p124 p125 p302 p303 p788 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h5066 : p788)
    (h15554 : p7 ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p125) ∨ p302 ∨ (¬ p303) ∨ (¬ p788)) : (¬ p101) ∨ (¬ p124) ∨ (¬ p125) ∨ (¬ p303) := by
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
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p302) := by
    exact h16285
  have u6 : p788 := by
    exact h5066
  rcases h15554 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step20097 (p7 p63 p224 p302 p792 p836 p923 p1099 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h4535 : p792)
    (h15555 : p7 ∨ (¬ p63) ∨ (¬ p224) ∨ p302 ∨ (¬ p792) ∨ (¬ p836) ∨ (¬ p923) ∨ (¬ p1099)) : (¬ p63) ∨ (¬ p224) ∨ (¬ p836) ∨ (¬ p923) ∨ (¬ p1099) := by
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
  have u2 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p923 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p302) := by
    exact h16285
  have u7 : p792 := by
    exact h4535
  rcases h15555 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step20098 (p7 p101 p124 p211 p1159 p1209 : Prop)
    (h16152 : (¬ p7))
    (h15556 : p7 ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p211) ∨ (¬ p1159) ∨ (¬ p1209)) : (¬ p101) ∨ (¬ p124) ∨ (¬ p211) ∨ (¬ p1159) ∨ (¬ p1209) := by
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
  have u2 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15556 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20099 (p7 p19 p224 p229 p302 p560 p710 p788 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h5066 : p788)
    (h15557 : p7 ∨ (¬ p19) ∨ (¬ p224) ∨ (¬ p229) ∨ p302 ∨ (¬ p560) ∨ (¬ p710) ∨ (¬ p788)) : (¬ p19) ∨ (¬ p224) ∨ (¬ p229) ∨ (¬ p560) ∨ (¬ p710) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p302) := by
    exact h16285
  have u7 : p788 := by
    exact h5066
  rcases h15557 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step20100 (p7 p17 p224 p258 p279 p302 p346 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16285 : (¬ p302))
    (h15558 : p7 ∨ (¬ p17) ∨ (¬ p224) ∨ (¬ p258) ∨ (¬ p279) ∨ p302 ∨ (¬ p346)) : (¬ p17) ∨ (¬ p224) ∨ (¬ p258) ∨ (¬ p346) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p279 := by
    exact h1444
  have u6 : (¬ p302) := by
    exact h16285
  rcases h15558 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step20101 (p7 p224 p261 p279 p304 p346 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16309 : (¬ p1324))
    (h15560 : p7 ∨ (¬ p224) ∨ (¬ p261) ∨ (¬ p279) ∨ (¬ p304) ∨ (¬ p346) ∨ p1324 ∨ (¬ p1325)) : (¬ p224) ∨ (¬ p261) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p279 := by
    exact h1444
  have u7 : (¬ p1324) := by
    exact h16309
  rcases h15560 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step20102 (p4 p7 p224 p261 p279 p288 p301 p302 p304 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16285 : (¬ p302))
    (h15561 : (¬ p4) ∨ p7 ∨ (¬ p224) ∨ (¬ p261) ∨ (¬ p279) ∨ (¬ p288) ∨ (¬ p301) ∨ p302 ∨ (¬ p304)) : (¬ p4) ∨ (¬ p224) ∨ (¬ p261) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p304) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : p279 := by
    exact h1444
  have u8 : (¬ p302) := by
    exact h16285
  rcases h15561 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u8 q7)
  · exact False.elim (q8 u5)

theorem step20103 (p7 p126 p224 p264 p304 p346 p364 p687 p1334 : Prop)
    (h16152 : (¬ p7))
    (h15562 : p7 ∨ (¬ p126) ∨ (¬ p224) ∨ (¬ p264) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p364) ∨ (¬ p687) ∨ (¬ p1334)) : (¬ p126) ∨ (¬ p224) ∨ (¬ p264) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p364) ∨ (¬ p687) ∨ (¬ p1334) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p264 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15562 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20104 (p7 p39 p88 p224 p261 p304 p346 p1000 p1146 p1225 p1465 : Prop)
    (h16152 : (¬ p7))
    (h15563 : p7 ∨ (¬ p39) ∨ (¬ p88) ∨ (¬ p224) ∨ (¬ p261) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p1000) ∨ (¬ p1146) ∨ (¬ p1225) ∨ (¬ p1465)) : (¬ p39) ∨ (¬ p88) ∨ (¬ p224) ∨ (¬ p261) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p1000) ∨ (¬ p1146) ∨ (¬ p1225) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p261 := by
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
  have u6 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1146 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h15563 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step20105 (p7 p63 p69 p210 p304 p346 p430 p734 p792 p1141 p1209 : Prop)
    (h16152 : (¬ p7))
    (h16180 : (¬ p430))
    (h4535 : p792)
    (h15564 : p7 ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p346) ∨ p430 ∨ (¬ p734) ∨ (¬ p792) ∨ (¬ p1141) ∨ (¬ p1209)) : (¬ p63) ∨ (¬ p69) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p734) ∨ (¬ p1141) ∨ (¬ p1209) := by
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
  have u2 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p430) := by
    exact h16180
  have u10 : p792 := by
    exact h4535
  rcases h15564 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step20106 (p7 p190 p261 p304 p346 p734 p1035 p1140 p1335 : Prop)
    (h16152 : (¬ p7))
    (h15565 : p7 ∨ (¬ p190) ∨ (¬ p261) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p734) ∨ (¬ p1035) ∨ (¬ p1140) ∨ (¬ p1335)) : (¬ p190) ∨ (¬ p261) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p734) ∨ (¬ p1035) ∨ (¬ p1140) ∨ (¬ p1335) := by
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
  have u2 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15565 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20107 (p7 p39 p88 p127 p224 p261 p302 p304 p346 p423 p788 p1159 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h5066 : p788)
    (h15566 : p7 ∨ (¬ p39) ∨ (¬ p88) ∨ (¬ p127) ∨ (¬ p224) ∨ (¬ p261) ∨ p302 ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p423) ∨ (¬ p788) ∨ (¬ p1159)) : (¬ p39) ∨ (¬ p88) ∨ (¬ p127) ∨ (¬ p224) ∨ (¬ p261) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p423) ∨ (¬ p1159) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p261 := by
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
  have u7 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p302) := by
    exact h16285
  have u11 : p788 := by
    exact h5066
  rcases h15566 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
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

theorem step20108 (p7 p15 p19 p141 p288 p304 p422 p500 p1209 : Prop)
    (h16152 : (¬ p7))
    (h15567 : p7 ∨ (¬ p15) ∨ (¬ p19) ∨ (¬ p141) ∨ (¬ p288) ∨ (¬ p304) ∨ (¬ p422) ∨ (¬ p500) ∨ (¬ p1209)) : (¬ p15) ∨ (¬ p19) ∨ (¬ p141) ∨ (¬ p288) ∨ (¬ p304) ∨ (¬ p422) ∨ (¬ p500) ∨ (¬ p1209) := by
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
  have u2 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15567 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20109 (p7 p39 p69 p88 p261 p303 p304 p345 p595 p657 p901 : Prop)
    (h16152 : (¬ p7))
    (h15568 : p7 ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p261) ∨ (¬ p303) ∨ (¬ p304) ∨ (¬ p345) ∨ (¬ p595) ∨ (¬ p657) ∨ (¬ p901)) : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p261) ∨ (¬ p303) ∨ (¬ p304) ∨ (¬ p345) ∨ (¬ p595) ∨ (¬ p657) ∨ (¬ p901) := by
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
  have u3 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p901 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h15568 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step20110 (p7 p234 p542 p657 p998 p1141 : Prop)
    (h16152 : (¬ p7))
    (h15569 : p7 ∨ (¬ p234) ∨ (¬ p542) ∨ (¬ p657) ∨ (¬ p998) ∨ (¬ p1141)) : (¬ p234) ∨ (¬ p542) ∨ (¬ p657) ∨ (¬ p998) ∨ (¬ p1141) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p998 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15569 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20111 (p7 p15 p16 p17 p234 p258 p346 p542 : Prop)
    (h16152 : (¬ p7))
    (h15570 : p7 ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p234) ∨ (¬ p258) ∨ (¬ p346) ∨ (¬ p542)) : (¬ p15) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p234) ∨ (¬ p258) ∨ (¬ p346) ∨ (¬ p542) := by
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
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p234 := by
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
  have u6 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15570 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20112 (p7 p70 p85 p918 p985 p1035 p1140 p1584 : Prop)
    (h16152 : (¬ p7))
    (h15571 : p7 ∨ (¬ p70) ∨ (¬ p85) ∨ (¬ p918) ∨ (¬ p985) ∨ (¬ p1035) ∨ (¬ p1140) ∨ (¬ p1584)) : (¬ p70) ∨ (¬ p85) ∨ (¬ p918) ∨ (¬ p985) ∨ (¬ p1035) ∨ (¬ p1140) ∨ (¬ p1584) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15571 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20113 (p7 p185 p279 p756 p1076 p1181 p1584 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16272 : (¬ p1181))
    (h15573 : p7 ∨ (¬ p185) ∨ (¬ p279) ∨ (¬ p756) ∨ (¬ p1076) ∨ p1181 ∨ (¬ p1584)) : (¬ p185) ∨ (¬ p756) ∨ (¬ p1076) ∨ (¬ p1584) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p279 := by
    exact h1444
  have u6 : (¬ p1181) := by
    exact h16272
  rcases h15573 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step20114 (p7 p87 p238 p537 p769 p928 : Prop)
    (h16152 : (¬ p7))
    (h15574 : p7 ∨ (¬ p87) ∨ (¬ p238) ∨ (¬ p537) ∨ (¬ p769) ∨ (¬ p928)) : (¬ p87) ∨ (¬ p238) ∨ (¬ p537) ∨ (¬ p769) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15574 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20115 (p7 p39 p69 p88 p261 p288 p301 p304 p595 p599 : Prop)
    (h16152 : (¬ p7))
    (h15575 : p7 ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p261) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p304) ∨ (¬ p595) ∨ (¬ p599)) : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p261) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p304) ∨ (¬ p595) ∨ (¬ p599) := by
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
  have u3 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p599 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15575 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step20117 (p7 p38 p49 p84 p101 p125 p206 p242 p323 p343 p686 p840 p1061 p1115 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16205 : (¬ p686))
    (h15577 : p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p101) ∨ (¬ p125) ∨ (¬ p206) ∨ (¬ p242) ∨ (¬ p323) ∨ (¬ p343) ∨ p686 ∨ (¬ p840) ∨ (¬ p1061) ∨ (¬ p1115)) : (¬ p38) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p101) ∨ (¬ p125) ∨ (¬ p206) ∨ (¬ p242) ∨ (¬ p323) ∨ (¬ p840) ∨ (¬ p1061) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
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
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : (¬ p7) := by
    exact h16152
  have u12 : p343 := by
    exact h1950
  have u13 : (¬ p686) := by
    exact h16205
  rcases h15577 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13
  · exact False.elim (u11 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u12)
  · exact False.elim (u13 q10)
  · exact False.elim (q11 u8)
  · exact False.elim (q12 u9)
  · exact False.elim (q13 u10)

theorem step20118 (p2 p7 p85 p88 p194 p387 p419 p595 p599 : Prop)
    (h16152 : (¬ p7))
    (h15578 : (¬ p2) ∨ p7 ∨ (¬ p85) ∨ (¬ p88) ∨ (¬ p194) ∨ (¬ p387) ∨ (¬ p419) ∨ (¬ p595) ∨ (¬ p599)) : (¬ p2) ∨ (¬ p85) ∨ (¬ p88) ∨ (¬ p194) ∨ (¬ p387) ∨ (¬ p419) ∨ (¬ p595) ∨ (¬ p599) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p599 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15578 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20119 (p6 p7 p10 p38 p49 p84 p242 p302 p303 p343 p840 p1061 p1115 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h1950 : p343)
    (h15579 : (¬ p6) ∨ p7 ∨ (¬ p10) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p242) ∨ p302 ∨ (¬ p303) ∨ (¬ p343) ∨ (¬ p840) ∨ (¬ p1061) ∨ (¬ p1115)) : (¬ p6) ∨ (¬ p10) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p242) ∨ (¬ p303) ∨ (¬ p840) ∨ (¬ p1061) ∨ (¬ p1115) := by
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
  have u2 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : (¬ p302) := by
    exact h16285
  have u12 : p343 := by
    exact h1950
  rcases h15579 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (q0 u0)
  · exact False.elim (u10 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u11 q7)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u12)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)
  · exact False.elim (q12 u9)

theorem step20120 (p7 p101 p323 p343 p434 p686 p734 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16205 : (¬ p686))
    (h15580 : p7 ∨ (¬ p101) ∨ (¬ p323) ∨ (¬ p343) ∨ (¬ p434) ∨ p686 ∨ (¬ p734)) : (¬ p101) ∨ (¬ p323) ∨ (¬ p434) ∨ (¬ p734) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p343 := by
    exact h1950
  have u6 : (¬ p686) := by
    exact h16205
  rcases h15580 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step20121 (p7 p11 p13 p14 p40 p85 p576 p980 p1035 p1042 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h7053 : p1184)
    (h15581 : p7 ∨ (¬ p11) ∨ (¬ p13) ∨ (¬ p14) ∨ p40 ∨ (¬ p85) ∨ (¬ p576) ∨ (¬ p980) ∨ (¬ p1035) ∨ (¬ p1042) ∨ (¬ p1184)) : (¬ p11) ∨ (¬ p13) ∨ (¬ p14) ∨ (¬ p85) ∨ (¬ p576) ∨ (¬ p980) ∨ (¬ p1035) ∨ (¬ p1042) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1042 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p40) := by
    exact h16150
  have u10 : p1184 := by
    exact h7053
  rcases h15581 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step20122 (p6 p7 p191 p1207 p1250 p1465 p1508 : Prop)
    (h16152 : (¬ p7))
    (h15582 : (¬ p6) ∨ p7 ∨ (¬ p191) ∨ (¬ p1207) ∨ (¬ p1250) ∨ (¬ p1465) ∨ (¬ p1508)) : (¬ p6) ∨ (¬ p191) ∨ (¬ p1207) ∨ (¬ p1250) ∨ (¬ p1465) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1250 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15582 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20123 (p7 p305 p344 p710 p757 p1631 : Prop)
    (h16152 : (¬ p7))
    (h15583 : p7 ∨ (¬ p305) ∨ (¬ p344) ∨ (¬ p710) ∨ (¬ p757) ∨ (¬ p1631)) : (¬ p305) ∨ (¬ p344) ∨ (¬ p710) ∨ (¬ p757) ∨ (¬ p1631) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p757 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1631 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15583 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20124 (p7 p18 p43 p71 p127 p1232 p1270 : Prop)
    (h16152 : (¬ p7))
    (h15584 : p7 ∨ (¬ p18) ∨ (¬ p43) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p1232) ∨ (¬ p1270)) : (¬ p18) ∨ (¬ p43) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p1232) ∨ (¬ p1270) := by
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
  have u2 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1270 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15584 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20125 (p7 p16 p160 p161 p185 p344 p638 p836 p1236 p1306 : Prop)
    (h16152 : (¬ p7))
    (h15585 : p7 ∨ (¬ p16) ∨ (¬ p160) ∨ (¬ p161) ∨ (¬ p185) ∨ (¬ p344) ∨ (¬ p638) ∨ (¬ p836) ∨ (¬ p1236) ∨ (¬ p1306)) : (¬ p16) ∨ (¬ p160) ∨ (¬ p161) ∨ (¬ p185) ∨ (¬ p344) ∨ (¬ p638) ∨ (¬ p836) ∨ (¬ p1236) ∨ (¬ p1306) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
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
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p638 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1236 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15585 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step20126 (p7 p18 p128 p210 p224 p302 p304 p346 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16285 : (¬ p302))
    (h15586 : p7 ∨ (¬ p18) ∨ (¬ p128) ∨ (¬ p210) ∨ (¬ p224) ∨ p302 ∨ (¬ p304) ∨ (¬ p346)) : (¬ p18) ∨ (¬ p210) ∨ (¬ p224) ∨ (¬ p304) ∨ (¬ p346) := by
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
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p128 := by
    exact h653
  have u7 : (¬ p302) := by
    exact h16285
  rcases h15586 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u7 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step20127 (p7 p18 p46 p170 p210 p305 p537 p769 : Prop)
    (h16152 : (¬ p7))
    (h15587 : p7 ∨ (¬ p18) ∨ (¬ p46) ∨ (¬ p170) ∨ (¬ p210) ∨ (¬ p305) ∨ (¬ p537) ∨ (¬ p769)) : (¬ p18) ∨ (¬ p46) ∨ (¬ p170) ∨ (¬ p210) ∨ (¬ p305) ∨ (¬ p537) ∨ (¬ p769) := by
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
  have u2 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15587 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20128 (p7 p18 p128 p210 p304 p346 p430 p734 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16180 : (¬ p430))
    (h15588 : p7 ∨ (¬ p18) ∨ (¬ p128) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p346) ∨ p430 ∨ (¬ p734)) : (¬ p18) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p734) := by
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
  have u3 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p128 := by
    exact h653
  have u7 : (¬ p430) := by
    exact h16180
  rcases h15588 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step20129 (p7 p101 p143 p286 p576 p928 : Prop)
    (h16152 : (¬ p7))
    (h15589 : p7 ∨ (¬ p101) ∨ (¬ p143) ∨ (¬ p286) ∨ (¬ p576) ∨ (¬ p928)) : (¬ p101) ∨ (¬ p143) ∨ (¬ p286) ∨ (¬ p576) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15589 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20130 (p430 p431 p1333 p1386 : Prop)
    (h16180 : (¬ p430))
    (h8348 : p1386)
    (h15590 : p430 ∨ p431 ∨ (¬ p1333) ∨ (¬ p1386)) : p431 ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p431) := fun hu => hn (Or.inl hu)
  have u1 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p430) := by
    exact h16180
  have u3 : p1386 := by
    exact h8348
  rcases h15590 with q0 | q1 | q2 | q3
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)

theorem step20131 (p7 p83 p185 p280 p301 p576 p928 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16173 : (¬ p280))
    (h7053 : p1184)
    (h15591 : p7 ∨ (¬ p83) ∨ (¬ p185) ∨ p280 ∨ (¬ p301) ∨ (¬ p576) ∨ (¬ p928) ∨ (¬ p1184)) : (¬ p83) ∨ (¬ p185) ∨ (¬ p301) ∨ (¬ p576) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p280) := by
    exact h16173
  have u7 : p1184 := by
    exact h7053
  rcases h15591 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step20132 (p7 p101 p124 p125 p126 p143 : Prop)
    (h16152 : (¬ p7))
    (h15592 : p7 ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p143)) : (¬ p101) ∨ (¬ p124) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p143) := by
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
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15592 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20133 (p7 p101 p426 p537 p726 p788 p836 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h5066 : p788)
    (h15593 : p7 ∨ (¬ p101) ∨ p426 ∨ (¬ p537) ∨ (¬ p726) ∨ (¬ p788) ∨ (¬ p836)) : (¬ p101) ∨ (¬ p537) ∨ (¬ p726) ∨ (¬ p836) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p726 := by
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
  have u6 : p788 := by
    exact h5066
  rcases h15593 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step20136 (p7 p8 p85 p106 p225 p258 p576 p1100 : Prop)
    (h16152 : (¬ p7))
    (h15596 : p7 ∨ (¬ p8) ∨ (¬ p85) ∨ (¬ p106) ∨ (¬ p225) ∨ (¬ p258) ∨ (¬ p576) ∨ (¬ p1100)) : (¬ p8) ∨ (¬ p85) ∨ (¬ p106) ∨ (¬ p225) ∨ (¬ p258) ∨ (¬ p576) ∨ (¬ p1100) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p106 := by
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
  have u5 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1100 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15596 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20137 (p3 p7 p70 p85 p544 p657 p864 p1249 : Prop)
    (h16152 : (¬ p7))
    (h15597 : (¬ p3) ∨ p7 ∨ (¬ p70) ∨ (¬ p85) ∨ (¬ p544) ∨ (¬ p657) ∨ (¬ p864) ∨ (¬ p1249)) : (¬ p3) ∨ (¬ p70) ∨ (¬ p85) ∨ (¬ p544) ∨ (¬ p657) ∨ (¬ p864) ∨ (¬ p1249) := by
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
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15597 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20138 (p7 p70 p85 p224 p481 p842 p996 p1385 : Prop)
    (h16152 : (¬ p7))
    (h15598 : p7 ∨ (¬ p70) ∨ (¬ p85) ∨ (¬ p224) ∨ (¬ p481) ∨ (¬ p842) ∨ (¬ p996) ∨ (¬ p1385)) : (¬ p70) ∨ (¬ p85) ∨ (¬ p224) ∨ (¬ p481) ∨ (¬ p842) ∨ (¬ p996) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p842 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15598 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20139 (p7 p126 p224 p258 p343 p364 p406 p686 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16205 : (¬ p686))
    (h15600 : p7 ∨ (¬ p126) ∨ (¬ p224) ∨ (¬ p258) ∨ (¬ p343) ∨ (¬ p364) ∨ (¬ p406) ∨ p686) : (¬ p126) ∨ (¬ p224) ∨ (¬ p258) ∨ (¬ p364) ∨ (¬ p406) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p343 := by
    exact h1950
  have u7 : (¬ p686) := by
    exact h16205
  rcases h15600 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step20140 (p7 p85 p224 p301 p351 p406 p576 p617 : Prop)
    (h16152 : (¬ p7))
    (h15601 : p7 ∨ (¬ p85) ∨ (¬ p224) ∨ (¬ p301) ∨ (¬ p351) ∨ (¬ p406) ∨ (¬ p576) ∨ (¬ p617)) : (¬ p85) ∨ (¬ p224) ∨ (¬ p301) ∨ (¬ p351) ∨ (¬ p406) ∨ (¬ p576) ∨ (¬ p617) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15601 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20141 (p7 p70 p85 p121 p127 p258 p576 p1084 : Prop)
    (h16152 : (¬ p7))
    (h15602 : p7 ∨ (¬ p70) ∨ (¬ p85) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p258) ∨ (¬ p576) ∨ (¬ p1084)) : (¬ p70) ∨ (¬ p85) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p258) ∨ (¬ p576) ∨ (¬ p1084) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15602 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20143 (p7 p125 p303 p441 p1334 p1631 : Prop)
    (h16152 : (¬ p7))
    (h15604 : p7 ∨ (¬ p125) ∨ (¬ p303) ∨ (¬ p441) ∨ (¬ p1334) ∨ (¬ p1631)) : (¬ p125) ∨ (¬ p303) ∨ (¬ p441) ∨ (¬ p1334) ∨ (¬ p1631) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p441 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1631 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15604 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20144 (p7 p15 p49 p84 p242 p285 p495 p636 p1061 p1115 : Prop)
    (h16152 : (¬ p7))
    (h15605 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p242) ∨ (¬ p285) ∨ (¬ p495) ∨ (¬ p636) ∨ (¬ p1061) ∨ (¬ p1115)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p242) ∨ (¬ p285) ∨ (¬ p495) ∨ (¬ p636) ∨ (¬ p1061) ∨ (¬ p1115) := by
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
  have u4 : p285 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p636 := by
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
  rcases h15605 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step20145 (p7 p15 p49 p84 p237 p616 p665 p1116 p1287 : Prop)
    (h16152 : (¬ p7))
    (h15606 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p237) ∨ (¬ p616) ∨ (¬ p665) ∨ (¬ p1116) ∨ (¬ p1287)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p237) ∨ (¬ p616) ∨ (¬ p665) ∨ (¬ p1116) ∨ (¬ p1287) := by
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
  have u4 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15606 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20146 (p7 p163 p193 p544 p657 p791 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16213 : (¬ p791))
    (h6744 : p1135)
    (h15607 : p7 ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p544) ∨ (¬ p657) ∨ p791 ∨ (¬ p1135)) : (¬ p163) ∨ (¬ p193) ∨ (¬ p544) ∨ (¬ p657) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p791) := by
    exact h16213
  have u6 : p1135 := by
    exact h6744
  rcases h15607 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step20147 (p7 p668 p897 p980 p1225 p1311 : Prop)
    (h16152 : (¬ p7))
    (h15608 : p7 ∨ (¬ p668) ∨ (¬ p897) ∨ (¬ p980) ∨ (¬ p1225) ∨ (¬ p1311)) : (¬ p668) ∨ (¬ p897) ∨ (¬ p980) ∨ (¬ p1225) ∨ (¬ p1311) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1311 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15608 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20148 (p7 p27 p70 p125 p142 p481 p494 p601 p796 : Prop)
    (h16152 : (¬ p7))
    (h15609 : p7 ∨ (¬ p27) ∨ (¬ p70) ∨ (¬ p125) ∨ (¬ p142) ∨ (¬ p481) ∨ (¬ p494) ∨ (¬ p601) ∨ (¬ p796)) : (¬ p27) ∨ (¬ p70) ∨ (¬ p125) ∨ (¬ p142) ∨ (¬ p481) ∨ (¬ p494) ∨ (¬ p601) ∨ (¬ p796) := by
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
  have u2 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p142 := by
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
  have u6 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15609 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20149 (p7 p70 p161 p163 p164 p481 p796 p983 p1181 p1232 : Prop)
    (h16152 : (¬ p7))
    (h789 : p164)
    (h16272 : (¬ p1181))
    (h15610 : p7 ∨ (¬ p70) ∨ (¬ p161) ∨ (¬ p163) ∨ (¬ p164) ∨ (¬ p481) ∨ (¬ p796) ∨ (¬ p983) ∨ p1181 ∨ (¬ p1232)) : (¬ p70) ∨ (¬ p161) ∨ (¬ p163) ∨ (¬ p481) ∨ (¬ p796) ∨ (¬ p983) ∨ (¬ p1232) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
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
  have u5 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p164 := by
    exact h789
  have u9 : (¬ p1181) := by
    exact h16272
  rcases h15610 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step20150 (p7 p101 p133 p141 p288 p481 p788 p796 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h5066 : p788)
    (h15611 : p7 ∨ (¬ p101) ∨ p133 ∨ (¬ p141) ∨ (¬ p288) ∨ (¬ p481) ∨ (¬ p788) ∨ (¬ p796)) : (¬ p101) ∨ (¬ p141) ∨ (¬ p288) ∨ (¬ p481) ∨ (¬ p796) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p288 := by
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
  have u6 : (¬ p133) := by
    exact h16157
  have u7 : p788 := by
    exact h5066
  rcases h15611 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step20151 (p7 p86 p789 p790 p985 p1099 p1333 p1538 : Prop)
    (h16152 : (¬ p7))
    (h15612 : p7 ∨ (¬ p86) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p985) ∨ (¬ p1099) ∨ (¬ p1333) ∨ (¬ p1538)) : (¬ p86) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p985) ∨ (¬ p1099) ∨ (¬ p1333) ∨ (¬ p1538) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p86 := by
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
  have u3 : p985 := by
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
  rcases h15612 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20152 (p7 p101 p124 p133 p481 p788 p796 p961 p1210 p1256 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h5066 : p788)
    (h15613 : p7 ∨ (¬ p101) ∨ (¬ p124) ∨ p133 ∨ (¬ p481) ∨ (¬ p788) ∨ (¬ p796) ∨ (¬ p961) ∨ (¬ p1210) ∨ (¬ p1256)) : (¬ p101) ∨ (¬ p124) ∨ (¬ p481) ∨ (¬ p796) ∨ (¬ p961) ∨ (¬ p1210) ∨ (¬ p1256) := by
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
  have u2 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p133) := by
    exact h16157
  have u9 : p788 := by
    exact h5066
  rcases h15613 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u8 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step20153 (p7 p85 p498 p582 p1604 p1631 : Prop)
    (h16152 : (¬ p7))
    (h15615 : p7 ∨ (¬ p85) ∨ (¬ p498) ∨ (¬ p582) ∨ (¬ p1604) ∨ (¬ p1631)) : (¬ p85) ∨ (¬ p498) ∨ (¬ p582) ∨ (¬ p1604) ∨ (¬ p1631) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1604 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1631 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15615 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20154 (p7 p255 p262 p581 p757 p918 p1631 : Prop)
    (h16152 : (¬ p7))
    (h15616 : p7 ∨ (¬ p255) ∨ (¬ p262) ∨ (¬ p581) ∨ (¬ p757) ∨ (¬ p918) ∨ (¬ p1631)) : (¬ p255) ∨ (¬ p262) ∨ (¬ p581) ∨ (¬ p757) ∨ (¬ p918) ∨ (¬ p1631) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p757 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1631 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15616 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20155 (p7 p45 p129 p1135 p1273 p1325 p1508 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h6744 : p1135)
    (h15617 : p7 ∨ (¬ p45) ∨ p129 ∨ (¬ p1135) ∨ (¬ p1273) ∨ (¬ p1325) ∨ (¬ p1508)) : (¬ p45) ∨ (¬ p1273) ∨ (¬ p1325) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1273 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p1135 := by
    exact h6744
  rcases h15617 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step20156 (p3 p7 p41 p187 p230 p544 p657 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6744 : p1135)
    (h15618 : (¬ p3) ∨ p7 ∨ (¬ p41) ∨ (¬ p187) ∨ p230 ∨ (¬ p544) ∨ (¬ p657) ∨ (¬ p1135)) : (¬ p3) ∨ (¬ p41) ∨ (¬ p187) ∨ (¬ p544) ∨ (¬ p657) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p1135 := by
    exact h6744
  rcases h15618 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step20157 (p7 p237 p791 p983 p1116 p1135 p1325 : Prop)
    (h16152 : (¬ p7))
    (h16213 : (¬ p791))
    (h6744 : p1135)
    (h15619 : p7 ∨ (¬ p237) ∨ p791 ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1135) ∨ (¬ p1325)) : (¬ p237) ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p237 := by
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
  have u5 : (¬ p791) := by
    exact h16213
  have u6 : p1135 := by
    exact h6744
  rcases h15619 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step20159 (p7 p11 p135 p170 p185 p227 p266 : Prop)
    (h16152 : (¬ p7))
    (h15621 : p7 ∨ (¬ p11) ∨ (¬ p135) ∨ (¬ p170) ∨ (¬ p185) ∨ (¬ p227) ∨ (¬ p266)) : (¬ p11) ∨ (¬ p135) ∨ (¬ p170) ∨ (¬ p185) ∨ (¬ p227) ∨ (¬ p266) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15621 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20160 (p7 p129 p170 p185 p256 p788 p1206 p1443 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h5066 : p788)
    (h15622 : p7 ∨ p129 ∨ (¬ p170) ∨ (¬ p185) ∨ (¬ p256) ∨ (¬ p788) ∨ (¬ p1206) ∨ (¬ p1443)) : (¬ p170) ∨ (¬ p185) ∨ (¬ p256) ∨ (¬ p1206) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p788 := by
    exact h5066
  rcases h15622 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step20161 (p1 p3 p7 p41 p187 p224 p230 p343 p996 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h1950 : p343)
    (h15623 : (¬ p1) ∨ (¬ p3) ∨ p7 ∨ (¬ p41) ∨ (¬ p187) ∨ (¬ p224) ∨ p230 ∨ (¬ p343) ∨ (¬ p996)) : (¬ p1) ∨ (¬ p3) ∨ (¬ p41) ∨ (¬ p187) ∨ (¬ p224) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p230) := by
    exact h16165
  have u8 : p343 := by
    exact h1950
  rcases h15623 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u5)

theorem step20162 (p7 p193 p224 p343 p424 p791 p996 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16213 : (¬ p791))
    (h15624 : p7 ∨ (¬ p193) ∨ (¬ p224) ∨ (¬ p343) ∨ (¬ p424) ∨ p791 ∨ (¬ p996)) : (¬ p193) ∨ (¬ p224) ∨ (¬ p424) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p424 := by
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
  have u6 : (¬ p791) := by
    exact h16213
  rcases h15624 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step20163 (p1 p7 p163 p193 p224 p343 p791 p996 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16213 : (¬ p791))
    (h15625 : (¬ p1) ∨ p7 ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p224) ∨ (¬ p343) ∨ p791 ∨ (¬ p996)) : (¬ p1) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p224) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p343 := by
    exact h1950
  have u7 : (¬ p791) := by
    exact h16213
  rcases h15625 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step20164 (p7 p105 p211 p226 p1631 p1666 : Prop)
    (h16152 : (¬ p7))
    (h15626 : p7 ∨ (¬ p105) ∨ (¬ p211) ∨ (¬ p226) ∨ (¬ p1631) ∨ (¬ p1666)) : (¬ p105) ∨ (¬ p211) ∨ (¬ p226) ∨ (¬ p1631) ∨ (¬ p1666) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1631 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15626 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20165 (p7 p426 p836 p1074 p1099 p1116 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h7053 : p1184)
    (h15628 : p7 ∨ p426 ∨ (¬ p836) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1116) ∨ (¬ p1184)) : (¬ p836) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p426) := by
    exact h16178
  have u6 : p1184 := by
    exact h7053
  rcases h15628 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step20166 (p2 p7 p229 p234 p653 p1140 p1708 : Prop)
    (h16152 : (¬ p7))
    (h16194 : (¬ p653))
    (h10766 : p1708)
    (h15629 : (¬ p2) ∨ p7 ∨ (¬ p229) ∨ (¬ p234) ∨ p653 ∨ (¬ p1140) ∨ (¬ p1708)) : (¬ p2) ∨ (¬ p229) ∨ (¬ p234) ∨ (¬ p1140) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p653) := by
    exact h16194
  have u6 : p1708 := by
    exact h10766
  rcases h15629 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step20167 (p7 p84 p105 p142 p166 p193 p918 : Prop)
    (h16152 : (¬ p7))
    (h15630 : p7 ∨ (¬ p84) ∨ (¬ p105) ∨ (¬ p142) ∨ (¬ p166) ∨ (¬ p193) ∨ (¬ p918)) : (¬ p84) ∨ (¬ p105) ∨ (¬ p142) ∨ (¬ p166) ∨ (¬ p193) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p84 := by
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
  have u3 : p166 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15630 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20168 (p7 p41 p142 p426 p788 p836 p918 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h5066 : p788)
    (h15631 : p7 ∨ (¬ p41) ∨ (¬ p142) ∨ p426 ∨ (¬ p788) ∨ (¬ p836) ∨ (¬ p918)) : (¬ p41) ∨ (¬ p142) ∨ (¬ p836) ∨ (¬ p918) := by
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
  have u2 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p426) := by
    exact h16178
  have u6 : p788 := by
    exact h5066
  rcases h15631 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step20169 (p7 p85 p344 p686 p836 p918 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h7053 : p1184)
    (h15632 : p7 ∨ (¬ p85) ∨ (¬ p344) ∨ p686 ∨ (¬ p836) ∨ (¬ p918) ∨ (¬ p1184)) : (¬ p85) ∨ (¬ p344) ∨ (¬ p836) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
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
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p686) := by
    exact h16205
  have u6 : p1184 := by
    exact h7053
  rcases h15632 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step20170 (p7 p132 p238 p256 p426 p836 p1055 p1116 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16178 : (¬ p426))
    (h15633 : p7 ∨ (¬ p132) ∨ (¬ p238) ∨ (¬ p256) ∨ p426 ∨ (¬ p836) ∨ (¬ p1055) ∨ (¬ p1116)) : (¬ p238) ∨ (¬ p256) ∨ (¬ p836) ∨ (¬ p1055) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p256 := by
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
  have u6 : p132 := by
    exact h786
  have u7 : (¬ p426) := by
    exact h16178
  rcases h15633 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step20171 (p7 p84 p135 p187 p256 p426 p481 p836 p918 p996 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h8348 : p1386)
    (h15634 : p7 ∨ (¬ p84) ∨ (¬ p135) ∨ (¬ p187) ∨ (¬ p256) ∨ p426 ∨ (¬ p481) ∨ (¬ p836) ∨ (¬ p918) ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p84) ∨ (¬ p135) ∨ (¬ p187) ∨ (¬ p256) ∨ (¬ p481) ∨ (¬ p836) ∨ (¬ p918) ∨ (¬ p996) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p84 := by
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
  have u3 : p256 := by
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
  have u6 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p426) := by
    exact h16178
  have u11 : p1386 := by
    exact h8348
  rcases h15634 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
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

theorem step20172 (p7 p164 p346 p426 p980 p1036 p1083 p1452 : Prop)
    (h16152 : (¬ p7))
    (h789 : p164)
    (h16178 : (¬ p426))
    (h15635 : p7 ∨ (¬ p164) ∨ (¬ p346) ∨ p426 ∨ (¬ p980) ∨ (¬ p1036) ∨ (¬ p1083) ∨ (¬ p1452)) : (¬ p346) ∨ (¬ p980) ∨ (¬ p1036) ∨ (¬ p1083) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1083 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p164 := by
    exact h789
  have u7 : (¬ p426) := by
    exact h16178
  rcases h15635 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (u7 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step20173 (p7 p84 p135 p256 p426 p435 p795 p836 p918 p996 p1022 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h6744 : p1135)
    (h15636 : p7 ∨ (¬ p84) ∨ (¬ p135) ∨ (¬ p256) ∨ p426 ∨ (¬ p435) ∨ (¬ p795) ∨ (¬ p836) ∨ (¬ p918) ∨ (¬ p996) ∨ (¬ p1022) ∨ (¬ p1135)) : (¬ p84) ∨ (¬ p135) ∨ (¬ p256) ∨ (¬ p435) ∨ (¬ p795) ∨ (¬ p836) ∨ (¬ p918) ∨ (¬ p996) ∨ (¬ p1022) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p795 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p836 := by
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
  have u8 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p426) := by
    exact h16178
  have u11 : p1135 := by
    exact h6744
  rcases h15636 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u10 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u8)
  · exact False.elim (q11 u11)

theorem step20174 (p7 p84 p121 p140 p255 p256 p918 p1084 : Prop)
    (h16152 : (¬ p7))
    (h15637 : p7 ∨ (¬ p84) ∨ (¬ p121) ∨ (¬ p140) ∨ (¬ p255) ∨ (¬ p256) ∨ (¬ p918) ∨ (¬ p1084)) : (¬ p84) ∨ (¬ p121) ∨ (¬ p140) ∨ (¬ p255) ∨ (¬ p256) ∨ (¬ p918) ∨ (¬ p1084) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15637 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20175 (p7 p45 p135 p265 p455 p580 p961 : Prop)
    (h16152 : (¬ p7))
    (h15638 : p7 ∨ (¬ p45) ∨ (¬ p135) ∨ (¬ p265) ∨ (¬ p455) ∨ (¬ p580) ∨ (¬ p961)) : (¬ p45) ∨ (¬ p135) ∨ (¬ p265) ∨ (¬ p455) ∨ (¬ p580) ∨ (¬ p961) := by
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
  have u3 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15638 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20176 (p7 p157 p160 p563 p980 p1036 : Prop)
    (h16152 : (¬ p7))
    (h15639 : p7 ∨ (¬ p157) ∨ (¬ p160) ∨ (¬ p563) ∨ (¬ p980) ∨ (¬ p1036)) : (¬ p157) ∨ (¬ p160) ∨ (¬ p563) ∨ (¬ p980) ∨ (¬ p1036) := by
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
  have u2 : p563 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15639 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20177 (p3 p7 p70 p389 p456 p495 p544 p657 : Prop)
    (h16152 : (¬ p7))
    (h15640 : (¬ p3) ∨ p7 ∨ (¬ p70) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p544) ∨ (¬ p657)) : (¬ p3) ∨ (¬ p70) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p544) ∨ (¬ p657) := by
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
  rcases h15640 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20178 (p7 p8 p12 p13 p225 p456 p495 p1100 : Prop)
    (h16152 : (¬ p7))
    (h15641 : p7 ∨ (¬ p8) ∨ (¬ p12) ∨ (¬ p13) ∨ (¬ p225) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p1100)) : (¬ p8) ∨ (¬ p12) ∨ (¬ p13) ∨ (¬ p225) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p1100) := by
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
  have u2 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
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
  have u6 : p1100 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15641 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20179 (p7 p172 p918 p1036 p1121 p1273 : Prop)
    (h16152 : (¬ p7))
    (h15642 : p7 ∨ (¬ p172) ∨ (¬ p918) ∨ (¬ p1036) ∨ (¬ p1121) ∨ (¬ p1273)) : (¬ p172) ∨ (¬ p918) ∨ (¬ p1036) ∨ (¬ p1121) ∨ (¬ p1273) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15642 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20180 (p7 p172 p185 p1036 p1121 p1346 : Prop)
    (h16152 : (¬ p7))
    (h15643 : p7 ∨ (¬ p172) ∨ (¬ p185) ∨ (¬ p1036) ∨ (¬ p1121) ∨ (¬ p1346)) : (¬ p172) ∨ (¬ p185) ∨ (¬ p1036) ∨ (¬ p1121) ∨ (¬ p1346) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15643 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20181 (p7 p45 p70 p129 p481 p494 p580 p996 p1333 p1386 p1611 p1624 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h8348 : p1386)
    (h15644 : p7 ∨ (¬ p45) ∨ (¬ p70) ∨ p129 ∨ (¬ p481) ∨ (¬ p494) ∨ (¬ p580) ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p1386) ∨ (¬ p1611) ∨ (¬ p1624)) : (¬ p45) ∨ (¬ p70) ∨ (¬ p481) ∨ (¬ p494) ∨ (¬ p580) ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p1611) ∨ (¬ p1624) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p580 := by
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
  have u10 : (¬ p129) := by
    exact h16154
  have u11 : p1386 := by
    exact h8348
  rcases h15644 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
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

theorem step20182 (p7 p70 p481 p495 p996 p1333 p1454 p1604 : Prop)
    (h16152 : (¬ p7))
    (h15645 : p7 ∨ (¬ p70) ∨ (¬ p481) ∨ (¬ p495) ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p1454) ∨ (¬ p1604)) : (¬ p70) ∨ (¬ p481) ∨ (¬ p495) ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p1454) ∨ (¬ p1604) := by
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
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p996 := by
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
  rcases h15645 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20183 (p7 p85 p864 p983 p1061 p1100 p1249 p1325 : Prop)
    (h16152 : (¬ p7))
    (h15646 : p7 ∨ (¬ p85) ∨ (¬ p864) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1100) ∨ (¬ p1249) ∨ (¬ p1325)) : (¬ p85) ∨ (¬ p864) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1100) ∨ (¬ p1249) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1100 := by
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
  rcases h15646 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20184 (p7 p41 p187 p230 p481 p996 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h8348 : p1386)
    (h15647 : p7 ∨ (¬ p41) ∨ (¬ p187) ∨ p230 ∨ (¬ p481) ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p41) ∨ (¬ p187) ∨ (¬ p481) ∨ (¬ p996) ∨ (¬ p1333) := by
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
  have u2 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p1386 := by
    exact h8348
  rcases h15647 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step20185 (p7 p8 p106 p225 p455 p494 p636 p961 p1100 : Prop)
    (h16152 : (¬ p7))
    (h15648 : p7 ∨ (¬ p8) ∨ (¬ p106) ∨ (¬ p225) ∨ (¬ p455) ∨ (¬ p494) ∨ (¬ p636) ∨ (¬ p961) ∨ (¬ p1100)) : (¬ p8) ∨ (¬ p106) ∨ (¬ p225) ∨ (¬ p455) ∨ (¬ p494) ∨ (¬ p636) ∨ (¬ p961) ∨ (¬ p1100) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1100 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15648 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20186 (p7 p135 p185 p256 p795 p862 p928 p1249 : Prop)
    (h16152 : (¬ p7))
    (h15649 : p7 ∨ (¬ p135) ∨ (¬ p185) ∨ (¬ p256) ∨ (¬ p795) ∨ (¬ p862) ∨ (¬ p928) ∨ (¬ p1249)) : (¬ p135) ∨ (¬ p185) ∨ (¬ p256) ∨ (¬ p795) ∨ (¬ p862) ∨ (¬ p928) ∨ (¬ p1249) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p795 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p862 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15649 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step20187 (p7 p41 p187 p230 p561 p983 p1061 p1135 p1325 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6744 : p1135)
    (h15650 : p7 ∨ (¬ p41) ∨ (¬ p187) ∨ p230 ∨ (¬ p561) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1135) ∨ (¬ p1325)) : (¬ p41) ∨ (¬ p187) ∨ (¬ p561) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1325) := by
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
  have u2 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p230) := by
    exact h16165
  have u8 : p1135 := by
    exact h6744
  rcases h15650 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u7 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u5)

theorem step20188 (p7 p185 p668 p836 p1121 p1346 : Prop)
    (h16152 : (¬ p7))
    (h15651 : p7 ∨ (¬ p185) ∨ (¬ p668) ∨ (¬ p836) ∨ (¬ p1121) ∨ (¬ p1346)) : (¬ p185) ∨ (¬ p668) ∨ (¬ p836) ∨ (¬ p1121) ∨ (¬ p1346) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15651 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20189 (p7 p17 p87 p158 p224 p351 p406 p420 p579 p680 p928 : Prop)
    (h16152 : (¬ p7))
    (h15652 : p7 ∨ (¬ p17) ∨ (¬ p87) ∨ (¬ p158) ∨ (¬ p224) ∨ (¬ p351) ∨ (¬ p406) ∨ (¬ p420) ∨ (¬ p579) ∨ (¬ p680) ∨ (¬ p928)) : (¬ p17) ∨ (¬ p87) ∨ (¬ p158) ∨ (¬ p224) ∨ (¬ p351) ∨ (¬ p406) ∨ (¬ p420) ∨ (¬ p579) ∨ (¬ p680) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p158 := by
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
  have u6 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h15652 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step20190 (p7 p25 p105 p210 p229 p455 p961 : Prop)
    (h16152 : (¬ p7))
    (h15653 : p7 ∨ (¬ p25) ∨ (¬ p105) ∨ (¬ p210) ∨ (¬ p229) ∨ (¬ p455) ∨ (¬ p961)) : (¬ p25) ∨ (¬ p105) ∨ (¬ p210) ∨ (¬ p229) ∨ (¬ p455) ∨ (¬ p961) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p25 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15653 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20191 (p7 p8 p17 p87 p158 p389 p456 p579 p657 p928 : Prop)
    (h16152 : (¬ p7))
    (h15654 : p7 ∨ (¬ p8) ∨ (¬ p17) ∨ (¬ p87) ∨ (¬ p158) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p579) ∨ (¬ p657) ∨ (¬ p928)) : (¬ p8) ∨ (¬ p17) ∨ (¬ p87) ∨ (¬ p158) ∨ (¬ p389) ∨ (¬ p456) ∨ (¬ p579) ∨ (¬ p657) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p158 := by
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
  have u6 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15654 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step20192 (p7 p41 p127 p187 p326 p798 p1385 : Prop)
    (h16152 : (¬ p7))
    (h15655 : p7 ∨ (¬ p41) ∨ (¬ p127) ∨ (¬ p187) ∨ (¬ p326) ∨ (¬ p798) ∨ (¬ p1385)) : (¬ p41) ∨ (¬ p127) ∨ (¬ p187) ∨ (¬ p326) ∨ (¬ p798) ∨ (¬ p1385) := by
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
  have u2 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p798 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15655 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20193 (p7 p105 p127 p544 p556 p710 : Prop)
    (h16152 : (¬ p7))
    (h15656 : p7 ∨ (¬ p105) ∨ (¬ p127) ∨ (¬ p544) ∨ (¬ p556) ∨ (¬ p710)) : (¬ p105) ∨ (¬ p127) ∨ (¬ p544) ∨ (¬ p556) ∨ (¬ p710) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
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
  rcases h15656 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20194 (p7 p17 p87 p406 p579 p636 p669 p816 p1076 p1393 : Prop)
    (h16152 : (¬ p7))
    (h15657 : p7 ∨ (¬ p17) ∨ (¬ p87) ∨ (¬ p406) ∨ (¬ p579) ∨ (¬ p636) ∨ (¬ p669) ∨ (¬ p816) ∨ (¬ p1076) ∨ (¬ p1393)) : (¬ p17) ∨ (¬ p87) ∨ (¬ p406) ∨ (¬ p579) ∨ (¬ p636) ∨ (¬ p669) ∨ (¬ p816) ∨ (¬ p1076) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15657 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step20195 (p7 p40 p304 p389 p423 p456 p494 p633 p1035 p1184 p1325 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h7053 : p1184)
    (h15658 : p7 ∨ p40 ∨ (¬ p304) ∨ (¬ p389) ∨ (¬ p423) ∨ (¬ p456) ∨ (¬ p494) ∨ (¬ p633) ∨ (¬ p1035) ∨ (¬ p1184) ∨ (¬ p1325)) : (¬ p304) ∨ (¬ p389) ∨ (¬ p423) ∨ (¬ p456) ∨ (¬ p494) ∨ (¬ p633) ∨ (¬ p1035) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p423 := by
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
  have u6 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p40) := by
    exact h16150
  have u10 : p1184 := by
    exact h7053
  rcases h15658 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (u9 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u10)
  · exact False.elim (q10 u7)

theorem step20196 (p7 p25 p210 p304 p326 p633 p1187 : Prop)
    (h16152 : (¬ p7))
    (h15659 : p7 ∨ (¬ p25) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p326) ∨ (¬ p633) ∨ (¬ p1187)) : (¬ p25) ∨ (¬ p210) ∨ (¬ p304) ∨ (¬ p326) ∨ (¬ p633) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p25 := by
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
  have u3 : p326 := by
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
  rcases h15659 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step20197 (p2 p7 p40 p85 p234 p918 p1040 p1115 p1140 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h7053 : p1184)
    (h15660 : (¬ p2) ∨ p7 ∨ p40 ∨ (¬ p85) ∨ (¬ p234) ∨ (¬ p918) ∨ (¬ p1040) ∨ (¬ p1115) ∨ (¬ p1140) ∨ (¬ p1184)) : (¬ p2) ∨ (¬ p85) ∨ (¬ p234) ∨ (¬ p918) ∨ (¬ p1040) ∨ (¬ p1115) ∨ (¬ p1140) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1040 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p40) := by
    exact h16150
  have u9 : p1184 := by
    exact h7053
  rcases h15660 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (u8 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u9)

theorem step20198 (p7 p40 p85 p234 p406 p476 p918 p985 p1184 p1333 p1584 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h7053 : p1184)
    (h15661 : p7 ∨ p40 ∨ (¬ p85) ∨ (¬ p234) ∨ (¬ p406) ∨ (¬ p476) ∨ (¬ p918) ∨ (¬ p985) ∨ (¬ p1184) ∨ (¬ p1333) ∨ (¬ p1584)) : (¬ p85) ∨ (¬ p234) ∨ (¬ p406) ∨ (¬ p476) ∨ (¬ p918) ∨ (¬ p985) ∨ (¬ p1333) ∨ (¬ p1584) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p234 := by
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
  have u4 : p918 := by
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
  have u7 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p40) := by
    exact h16150
  have u10 : p1184 := by
    exact h7053
  rcases h15661 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (u9 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step20199 (p7 p11 p13 p85 p162 p576 p710 p840 p1061 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16160 : (¬ p162))
    (h7053 : p1184)
    (h15662 : p7 ∨ (¬ p11) ∨ (¬ p13) ∨ (¬ p85) ∨ p162 ∨ (¬ p576) ∨ (¬ p710) ∨ (¬ p840) ∨ (¬ p1061) ∨ (¬ p1184)) : (¬ p11) ∨ (¬ p13) ∨ (¬ p85) ∨ (¬ p576) ∨ (¬ p710) ∨ (¬ p840) ∨ (¬ p1061) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p162) := by
    exact h16160
  have u9 : p1184 := by
    exact h7053
  rcases h15662 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step20200 (p7 p17 p83 p224 p406 p581 p617 p842 p1385 : Prop)
    (h16152 : (¬ p7))
    (h15663 : p7 ∨ (¬ p17) ∨ (¬ p83) ∨ (¬ p224) ∨ (¬ p406) ∨ (¬ p581) ∨ (¬ p617) ∨ (¬ p842) ∨ (¬ p1385)) : (¬ p17) ∨ (¬ p83) ∨ (¬ p224) ∨ (¬ p406) ∨ (¬ p581) ∨ (¬ p617) ∨ (¬ p842) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p83 := by
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
  have u4 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p617 := by
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
  rcases h15663 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20201 (p7 p8 p17 p83 p581 p657 p864 p1100 p1249 : Prop)
    (h16152 : (¬ p7))
    (h15664 : p7 ∨ (¬ p8) ∨ (¬ p17) ∨ (¬ p83) ∨ (¬ p581) ∨ (¬ p657) ∨ (¬ p864) ∨ (¬ p1100) ∨ (¬ p1249)) : (¬ p8) ∨ (¬ p17) ∨ (¬ p83) ∨ (¬ p581) ∨ (¬ p657) ∨ (¬ p864) ∨ (¬ p1100) ∨ (¬ p1249) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1100 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15664 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step20202 (p2 p7 p121 p122 p127 p129 p424 : Prop)
    (h16152 : (¬ p7))
    (h10260 : p122)
    (h16154 : (¬ p129))
    (h15665 : (¬ p2) ∨ p7 ∨ (¬ p121) ∨ (¬ p122) ∨ (¬ p127) ∨ p129 ∨ (¬ p424)) : (¬ p2) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p424) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
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
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p122 := by
    exact h10260
  have u6 : (¬ p129) := by
    exact h16154
  rcases h15665 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step20203 (p7 p11 p17 p83 p280 p420 p455 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16173 : (¬ p280))
    (h7053 : p1184)
    (h15666 : p7 ∨ (¬ p11) ∨ (¬ p17) ∨ (¬ p83) ∨ p280 ∨ (¬ p420) ∨ (¬ p455) ∨ (¬ p1184)) : (¬ p11) ∨ (¬ p17) ∨ (¬ p83) ∨ (¬ p420) ∨ (¬ p455) := by
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
  have u2 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p280) := by
    exact h16173
  have u7 : p1184 := by
    exact h7053
  rcases h15666 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step20204 (p2 p7 p129 p161 p424 p1140 p1184 p1210 p1232 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h7053 : p1184)
    (h15667 : (¬ p2) ∨ p7 ∨ p129 ∨ (¬ p161) ∨ (¬ p424) ∨ (¬ p1140) ∨ (¬ p1184) ∨ (¬ p1210) ∨ (¬ p1232) ∨ (¬ p1452)) : (¬ p2) ∨ (¬ p161) ∨ (¬ p424) ∨ (¬ p1140) ∨ (¬ p1210) ∨ (¬ p1232) ∨ (¬ p1452) := by
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
  have u2 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1210 := by
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
  have u8 : (¬ p129) := by
    exact h16154
  have u9 : p1184 := by
    exact h7053
  rcases h15667 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (u8 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step20205 (p2 p7 p17 p83 p129 p424 p581 p1140 p1184 p1249 p1258 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h7053 : p1184)
    (h15668 : (¬ p2) ∨ p7 ∨ (¬ p17) ∨ (¬ p83) ∨ p129 ∨ (¬ p424) ∨ (¬ p581) ∨ (¬ p1140) ∨ (¬ p1184) ∨ (¬ p1249) ∨ (¬ p1258)) : (¬ p2) ∨ (¬ p17) ∨ (¬ p83) ∨ (¬ p424) ∨ (¬ p581) ∨ (¬ p1140) ∨ (¬ p1249) ∨ (¬ p1258) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p129) := by
    exact h16154
  have u10 : p1184 := by
    exact h7053
  rcases h15668 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u9 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step20206 (p7 p8 p456 p495 p532 p728 p1100 p1330 : Prop)
    (h16152 : (¬ p7))
    (h15669 : p7 ∨ (¬ p8) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p532) ∨ (¬ p728) ∨ (¬ p1100) ∨ (¬ p1330)) : (¬ p8) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p532) ∨ (¬ p728) ∨ (¬ p1100) ∨ (¬ p1330) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1100 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15669 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

#print axioms step20206

end NineRUPTrial
