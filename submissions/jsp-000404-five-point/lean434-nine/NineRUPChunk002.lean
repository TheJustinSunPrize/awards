import Mathlib.Tactic.Tauto

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineRUPTrial

theorem step17334 (p430 p980 p1139 p1335 : Prop)
    (h16180 : (¬ p430))
    (h6761 : p1139)
    (h12165 : p430 ∨ (¬ p980) ∨ (¬ p1139) ∨ p1335) : (¬ p980) ∨ p1335 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1335) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p430) := by
    exact h16180
  have u3 : p1139 := by
    exact h6761
  rcases h12165 with q0 | q1 | q2 | q3
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (u1 q3)

theorem step17335 (p6 p7 p13 p14 p24 p67 p456 p980 p1035 p1042 : Prop)
    (h16152 : (¬ p7))
    (h12166 : (¬ p6) ∨ p7 ∨ (¬ p13) ∨ (¬ p14) ∨ (¬ p24) ∨ (¬ p67) ∨ (¬ p456) ∨ (¬ p980) ∨ (¬ p1035) ∨ (¬ p1042)) : (¬ p6) ∨ (¬ p13) ∨ (¬ p14) ∨ (¬ p24) ∨ (¬ p67) ∨ (¬ p456) ∨ (¬ p980) ∨ (¬ p1035) ∨ (¬ p1042) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
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
  have u3 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1042 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h12166 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17336 (p3 p7 p48 p68 p142 p167 p426 p499 p582 p788 p897 p1099 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h5066 : p788)
    (h12167 : (¬ p3) ∨ p7 ∨ (¬ p48) ∨ (¬ p68) ∨ (¬ p142) ∨ (¬ p167) ∨ p426 ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p788) ∨ (¬ p897) ∨ (¬ p1099)) : (¬ p3) ∨ (¬ p48) ∨ (¬ p68) ∨ (¬ p142) ∨ (¬ p167) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p897) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p167 := by
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
  have u7 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p426) := by
    exact h16178
  have u11 : p788 := by
    exact h5066
  rcases h12167 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u0)
  · exact False.elim (u9 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u10 q6)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u11)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step17338 (p494 p495 p500 p1160 p1184 : Prop)
    (h16265 : (¬ p1160))
    (h7053 : p1184)
    (h12174 : (¬ p494) ∨ (¬ p495) ∨ p500 ∨ p1160 ∨ (¬ p1184)) : (¬ p494) ∨ (¬ p495) ∨ p500 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p500) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1160) := by
    exact h16265
  have u4 : p1184 := by
    exact h7053
  rcases h12174 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (u3 q3)
  · exact False.elim (q4 u4)

theorem step17339 (p7 p63 p500 p532 p961 p1022 p1330 p1393 : Prop)
    (h16152 : (¬ p7))
    (h12175 : p7 ∨ (¬ p63) ∨ (¬ p500) ∨ (¬ p532) ∨ (¬ p961) ∨ (¬ p1022) ∨ (¬ p1330) ∨ (¬ p1393)) : (¬ p63) ∨ (¬ p500) ∨ (¬ p532) ∨ (¬ p961) ∨ (¬ p1022) ∨ (¬ p1330) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p500 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12175 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17340 (p308 p686 p1061 p1139 : Prop)
    (h16205 : (¬ p686))
    (h6761 : p1139)
    (h12177 : p308 ∨ p686 ∨ (¬ p1061) ∨ (¬ p1139)) : p308 ∨ (¬ p1061) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p308) := fun hu => hn (Or.inl hu)
  have u1 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p686) := by
    exact h16205
  have u3 : p1139 := by
    exact h6761
  rcases h12177 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)

theorem step17342 (p7 p455 p636 p726 p981 p1082 : Prop)
    (h16152 : (¬ p7))
    (h12179 : p7 ∨ (¬ p455) ∨ (¬ p636) ∨ (¬ p726) ∨ (¬ p981) ∨ (¬ p1082)) : (¬ p455) ∨ (¬ p636) ∨ (¬ p726) ∨ (¬ p981) ∨ (¬ p1082) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p981 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1082 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12179 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17343 (p7 p27 p104 p142 p192 p226 p633 : Prop)
    (h16152 : (¬ p7))
    (h12180 : p7 ∨ (¬ p27) ∨ (¬ p104) ∨ (¬ p142) ∨ (¬ p192) ∨ (¬ p226) ∨ (¬ p633)) : (¬ p27) ∨ (¬ p104) ∨ (¬ p142) ∨ (¬ p192) ∨ (¬ p226) ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p27 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12180 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17344 (p7 p127 p226 p686 p756 p788 p940 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h5066 : p788)
    (h12181 : p7 ∨ (¬ p127) ∨ (¬ p226) ∨ p686 ∨ (¬ p756) ∨ (¬ p788) ∨ (¬ p940)) : (¬ p127) ∨ (¬ p226) ∨ (¬ p756) ∨ (¬ p940) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p686) := by
    exact h16205
  have u6 : p788 := by
    exact h5066
  rcases h12181 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step17345 (p7 p86 p456 p495 p532 p790 p1022 p1330 : Prop)
    (h16152 : (¬ p7))
    (h12184 : p7 ∨ (¬ p86) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p532) ∨ (¬ p790) ∨ (¬ p1022) ∨ (¬ p1330)) : (¬ p86) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p532) ∨ (¬ p790) ∨ (¬ p1022) ∨ (¬ p1330) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p86 := by
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
  have u4 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12184 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17346 (p7 p195 p481 p797 p1015 p1366 : Prop)
    (h16152 : (¬ p7))
    (h12185 : p7 ∨ (¬ p195) ∨ (¬ p481) ∨ (¬ p797) ∨ (¬ p1015) ∨ (¬ p1366)) : (¬ p195) ∨ (¬ p481) ∨ (¬ p797) ∨ (¬ p1015) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p797 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12185 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17348 (p4 p7 p124 p125 p255 p668 p1116 : Prop)
    (h16152 : (¬ p7))
    (h12187 : (¬ p4) ∨ p7 ∨ (¬ p124) ∨ (¬ p125) ∨ (¬ p255) ∨ (¬ p668) ∨ (¬ p1116)) : (¬ p4) ∨ (¬ p124) ∨ (¬ p125) ∨ (¬ p255) ∨ (¬ p668) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p4 := by
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
  have u3 : p255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12187 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17349 (p2 p7 p102 p127 p875 p1077 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16220 : (¬ p875))
    (h6761 : p1139)
    (h12188 : (¬ p2) ∨ p7 ∨ (¬ p102) ∨ (¬ p127) ∨ p875 ∨ (¬ p1077) ∨ (¬ p1139)) : (¬ p2) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p875) := by
    exact h16220
  have u6 : p1139 := by
    exact h6761
  rcases h12188 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17350 (p2 p7 p127 p134 p875 p1256 p1708 : Prop)
    (h16152 : (¬ p7))
    (h16220 : (¬ p875))
    (h10766 : p1708)
    (h12189 : (¬ p2) ∨ p7 ∨ (¬ p127) ∨ (¬ p134) ∨ p875 ∨ (¬ p1256) ∨ (¬ p1708)) : (¬ p2) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p1256) := by
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
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p875) := by
    exact h16220
  have u6 : p1708 := by
    exact h10766
  rcases h12189 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17351 (p1000 p1324 p1325 p1708 : Prop)
    (h16309 : (¬ p1324))
    (h10766 : p1708)
    (h12191 : p1000 ∨ p1324 ∨ (¬ p1325) ∨ (¬ p1708)) : p1000 ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1000) := fun hu => hn (Or.inl hu)
  have u1 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1324) := by
    exact h16309
  have u3 : p1708 := by
    exact h10766
  rcases h12191 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)

theorem step17352 (p7 p431 p666 p734 p836 p1116 : Prop)
    (h16152 : (¬ p7))
    (h12195 : p7 ∨ (¬ p431) ∨ (¬ p666) ∨ (¬ p734) ∨ (¬ p836) ∨ (¬ p1116)) : (¬ p431) ∨ (¬ p666) ∨ (¬ p734) ∨ (¬ p836) ∨ (¬ p1116) := by
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
  have u2 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12195 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17354 (p15 p42 p50 p1136 : Prop)
    (h132 : p42)
    (h16259 : (¬ p1136))
    (h12200 : (¬ p15) ∨ (¬ p42) ∨ p50 ∨ p1136) : (¬ p15) ∨ p50 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p50) := fun hu => hn (Or.inr hu)
  have u2 : p42 := by
    exact h132
  have u3 : (¬ p1136) := by
    exact h16259
  rcases h12200 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u3 q3)

theorem step17355 (p7 p14 p15 p544 p657 p1135 p1136 : Prop)
    (h16152 : (¬ p7))
    (h6744 : p1135)
    (h16259 : (¬ p1136))
    (h12202 : p7 ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p544) ∨ (¬ p657) ∨ (¬ p1135) ∨ p1136) : (¬ p14) ∨ (¬ p15) ∨ (¬ p544) ∨ (¬ p657) := by
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
  have u5 : p1135 := by
    exact h6744
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h12202 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)

theorem step17356 (p7 p12 p14 p44 p90 p193 p241 p668 p710 p918 : Prop)
    (h16152 : (¬ p7))
    (h12203 : p7 ∨ (¬ p12) ∨ (¬ p14) ∨ (¬ p44) ∨ (¬ p90) ∨ (¬ p193) ∨ (¬ p241) ∨ (¬ p668) ∨ (¬ p710) ∨ (¬ p918)) : (¬ p12) ∨ (¬ p14) ∨ (¬ p44) ∨ (¬ p90) ∨ (¬ p193) ∨ (¬ p241) ∨ (¬ p668) ∨ (¬ p710) ∨ (¬ p918) := by
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
  have u2 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h12203 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17357 (p7 p45 p105 p140 p167 p581 : Prop)
    (h16152 : (¬ p7))
    (h12206 : p7 ∨ (¬ p45) ∨ (¬ p105) ∨ (¬ p140) ∨ (¬ p167) ∨ (¬ p581)) : (¬ p45) ∨ (¬ p105) ∨ (¬ p140) ∨ (¬ p167) ∨ (¬ p581) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12206 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17358 (p7 p45 p193 p343 p791 p840 p928 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16213 : (¬ p791))
    (h12207 : p7 ∨ (¬ p45) ∨ (¬ p193) ∨ (¬ p343) ∨ p791 ∨ (¬ p840) ∨ (¬ p928)) : (¬ p45) ∨ (¬ p193) ∨ (¬ p840) ∨ (¬ p928) := by
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
  have u2 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p343 := by
    exact h1950
  have u6 : (¬ p791) := by
    exact h16213
  rcases h12207 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17359 (p7 p45 p193 p791 p836 p904 p927 p1537 : Prop)
    (h16152 : (¬ p7))
    (h16213 : (¬ p791))
    (h9400 : p1537)
    (h12208 : p7 ∨ (¬ p45) ∨ (¬ p193) ∨ p791 ∨ (¬ p836) ∨ (¬ p904) ∨ (¬ p927) ∨ (¬ p1537)) : (¬ p45) ∨ (¬ p193) ∨ (¬ p836) ∨ (¬ p904) ∨ (¬ p927) := by
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
  have u2 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p791) := by
    exact h16213
  have u7 : p1537 := by
    exact h9400
  rcases h12208 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step17360 (p7 p14 p15 p142 p167 p788 p1136 : Prop)
    (h16152 : (¬ p7))
    (h5066 : p788)
    (h16259 : (¬ p1136))
    (h12209 : p7 ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p142) ∨ (¬ p167) ∨ (¬ p788) ∨ p1136) : (¬ p14) ∨ (¬ p15) ∨ (¬ p142) ∨ (¬ p167) := by
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
  have u2 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p788 := by
    exact h5066
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h12209 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)

theorem step17361 (p7 p142 p167 p344 p686 p788 p883 p897 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h5066 : p788)
    (h12211 : p7 ∨ (¬ p142) ∨ (¬ p167) ∨ (¬ p344) ∨ p686 ∨ (¬ p788) ∨ (¬ p883) ∨ (¬ p897)) : (¬ p142) ∨ (¬ p167) ∨ (¬ p344) ∨ (¬ p883) ∨ (¬ p897) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p686) := by
    exact h16205
  have u7 : p788 := by
    exact h5066
  rcases h12211 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17362 (p6 p7 p19 p344 p540 p659 p686 p1187 : Prop)
    (h16152 : (¬ p7))
    (h3753 : p659)
    (h16205 : (¬ p686))
    (h12213 : (¬ p6) ∨ p7 ∨ (¬ p19) ∨ (¬ p344) ∨ (¬ p540) ∨ (¬ p659) ∨ p686 ∨ (¬ p1187)) : (¬ p6) ∨ (¬ p19) ∨ (¬ p344) ∨ (¬ p540) ∨ (¬ p1187) := by
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
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p659 := by
    exact h3753
  have u7 : (¬ p686) := by
    exact h16205
  rcases h12213 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step17363 (p7 p15 p49 p84 p126 p256 p347 p897 p1099 : Prop)
    (h16152 : (¬ p7))
    (h12215 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p126) ∨ (¬ p256) ∨ (¬ p347) ∨ (¬ p897) ∨ (¬ p1099)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p126) ∨ (¬ p256) ∨ (¬ p347) ∨ (¬ p897) ∨ (¬ p1099) := by
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
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12215 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17364 (p7 p138 p165 p576 p927 p1095 p1115 : Prop)
    (h16152 : (¬ p7))
    (h12217 : p7 ∨ (¬ p138) ∨ (¬ p165) ∨ (¬ p576) ∨ (¬ p927) ∨ (¬ p1095) ∨ (¬ p1115)) : (¬ p138) ∨ (¬ p165) ∨ (¬ p576) ∨ (¬ p927) ∨ (¬ p1095) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p165 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12217 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17365 (p7 p18 p69 p101 p346 p426 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h7053 : p1184)
    (h12218 : p7 ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p101) ∨ (¬ p346) ∨ p426 ∨ (¬ p1184)) : (¬ p18) ∨ (¬ p69) ∨ (¬ p101) ∨ (¬ p346) := by
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
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p426) := by
    exact h16178
  have u6 : p1184 := by
    exact h7053
  rcases h12218 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step17366 (p7 p142 p185 p193 p230 p788 p928 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h5066 : p788)
    (h12219 : p7 ∨ (¬ p142) ∨ (¬ p185) ∨ (¬ p193) ∨ p230 ∨ (¬ p788) ∨ (¬ p928)) : (¬ p142) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p142 := by
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
  have u3 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p788 := by
    exact h5066
  rcases h12219 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step17367 (p7 p42 p185 p193 p225 p230 p262 p347 p368 p438 p581 p687 p880 p926 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16165 : (¬ p230))
    (h12220 : p7 ∨ (¬ p42) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p225) ∨ p230 ∨ (¬ p262) ∨ (¬ p347) ∨ (¬ p368) ∨ (¬ p438) ∨ (¬ p581) ∨ (¬ p687) ∨ (¬ p880) ∨ (¬ p926)) : (¬ p185) ∨ (¬ p193) ∨ (¬ p225) ∨ (¬ p262) ∨ (¬ p347) ∨ (¬ p368) ∨ (¬ p438) ∨ (¬ p581) ∨ (¬ p687) ∨ (¬ p880) ∨ (¬ p926) := by
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
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p262 := by
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
  have u6 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : (¬ p7) := by
    exact h16152
  have u12 : p42 := by
    exact h132
  have u13 : (¬ p230) := by
    exact h16165
  rcases h12220 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13
  · exact False.elim (u11 q0)
  · exact False.elim (q1 u12)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u13 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)
  · exact False.elim (q12 u9)
  · exact False.elim (q13 u10)

theorem step17368 (p7 p288 p342 p515 p581 p1385 : Prop)
    (h16152 : (¬ p7))
    (h12221 : p7 ∨ (¬ p288) ∨ (¬ p342) ∨ (¬ p515) ∨ (¬ p581) ∨ (¬ p1385)) : (¬ p288) ∨ (¬ p342) ∨ (¬ p515) ∨ (¬ p581) ∨ (¬ p1385) := by
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
  rcases h12221 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17369 (p7 p165 p242 p799 p814 p1061 p1115 : Prop)
    (h16152 : (¬ p7))
    (h12222 : p7 ∨ (¬ p165) ∨ (¬ p242) ∨ (¬ p799) ∨ (¬ p814) ∨ (¬ p1061) ∨ (¬ p1115)) : (¬ p165) ∨ (¬ p242) ∨ (¬ p799) ∨ (¬ p814) ∨ (¬ p1061) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p165 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p799 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12222 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17370 (p6 p7 p19 p48 p192 p799 p1385 : Prop)
    (h16152 : (¬ p7))
    (h12223 : (¬ p6) ∨ p7 ∨ (¬ p19) ∨ (¬ p48) ∨ (¬ p192) ∨ (¬ p799) ∨ (¬ p1385)) : (¬ p6) ∨ (¬ p19) ∨ (¬ p48) ∨ (¬ p192) ∨ (¬ p799) ∨ (¬ p1385) := by
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
  have u3 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p799 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12223 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17371 (p7 p265 p304 p516 p580 p633 p1385 : Prop)
    (h16152 : (¬ p7))
    (h12224 : p7 ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p516) ∨ (¬ p580) ∨ (¬ p633) ∨ (¬ p1385)) : (¬ p265) ∨ (¬ p304) ∨ (¬ p516) ∨ (¬ p580) ∨ (¬ p633) ∨ (¬ p1385) := by
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
  have u2 : p516 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12224 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17373 (p7 p309 p342 p420 p640 p1055 p1095 : Prop)
    (h16152 : (¬ p7))
    (h12226 : p7 ∨ (¬ p309) ∨ (¬ p342) ∨ (¬ p420) ∨ (¬ p640) ∨ (¬ p1055) ∨ (¬ p1095)) : (¬ p309) ∨ (¬ p342) ∨ (¬ p420) ∨ (¬ p640) ∨ (¬ p1055) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p342 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p640 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12226 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17374 (p7 p426 p690 p709 p728 p1061 p1075 p1076 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h6478 : p1075)
    (h12229 : p7 ∨ p426 ∨ (¬ p690) ∨ (¬ p709) ∨ (¬ p728) ∨ (¬ p1061) ∨ (¬ p1075) ∨ (¬ p1076)) : (¬ p690) ∨ (¬ p709) ∨ (¬ p728) ∨ (¬ p1061) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p426) := by
    exact h16178
  have u7 : p1075 := by
    exact h6478
  rcases h12229 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step17375 (p7 p14 p50 p165 p557 p1061 p1115 : Prop)
    (h16152 : (¬ p7))
    (h12230 : p7 ∨ (¬ p14) ∨ (¬ p50) ∨ (¬ p165) ∨ (¬ p557) ∨ (¬ p1061) ∨ (¬ p1115)) : (¬ p14) ∨ (¬ p50) ∨ (¬ p165) ∨ (¬ p557) ∨ (¬ p1061) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p50 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p165 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12230 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17377 (p7 p86 p256 p288 p668 p897 p1077 p1099 : Prop)
    (h16152 : (¬ p7))
    (h12235 : p7 ∨ (¬ p86) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p668) ∨ (¬ p897) ∨ (¬ p1077) ∨ (¬ p1099)) : (¬ p86) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p668) ∨ (¬ p897) ∨ (¬ p1077) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12235 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17378 (p7 p344 p686 p728 p834 p1015 p1116 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h6761 : p1139)
    (h12237 : p7 ∨ (¬ p344) ∨ p686 ∨ (¬ p728) ∨ (¬ p834) ∨ (¬ p1015) ∨ (¬ p1116) ∨ (¬ p1139)) : (¬ p344) ∨ (¬ p728) ∨ (¬ p834) ∨ (¬ p1015) ∨ (¬ p1116) := by
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
  have u2 : p834 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p686) := by
    exact h16205
  have u7 : p1139 := by
    exact h6761
  rcases h12237 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step17379 (p7 p15 p19 p102 p343 p344 p1136 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16259 : (¬ p1136))
    (h12238 : p7 ∨ (¬ p15) ∨ (¬ p19) ∨ (¬ p102) ∨ (¬ p343) ∨ (¬ p344) ∨ p1136) : (¬ p15) ∨ (¬ p19) ∨ (¬ p102) ∨ (¬ p344) := by
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
  have u2 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p343 := by
    exact h1950
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h12238 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step17380 (p15 p128 p614 p621 p1136 : Prop)
    (h653 : p128)
    (h16259 : (¬ p1136))
    (h12241 : (¬ p15) ∨ (¬ p128) ∨ (¬ p614) ∨ p621 ∨ p1136) : (¬ p15) ∨ (¬ p614) ∨ p621 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p614 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p621) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p128 := by
    exact h653
  have u4 : (¬ p1136) := by
    exact h16259
  rcases h12241 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (u2 q3)
  · exact False.elim (u4 q4)

theorem step17383 (p7 p14 p44 p90 p193 p544 p727 p918 p1584 : Prop)
    (h16152 : (¬ p7))
    (h12244 : p7 ∨ (¬ p14) ∨ (¬ p44) ∨ (¬ p90) ∨ (¬ p193) ∨ (¬ p544) ∨ (¬ p727) ∨ (¬ p918) ∨ (¬ p1584)) : (¬ p14) ∨ (¬ p44) ∨ (¬ p90) ∨ (¬ p193) ∨ (¬ p544) ∨ (¬ p727) ∨ (¬ p918) ∨ (¬ p1584) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p727 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12244 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17384 (p7 p237 p343 p537 p544 p791 p940 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16213 : (¬ p791))
    (h12246 : p7 ∨ (¬ p237) ∨ (¬ p343) ∨ (¬ p537) ∨ (¬ p544) ∨ p791 ∨ (¬ p940)) : (¬ p237) ∨ (¬ p537) ∨ (¬ p544) ∨ (¬ p940) := by
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
  have u2 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p343 := by
    exact h1950
  have u6 : (¬ p791) := by
    exact h16213
  rcases h12246 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step17385 (p7 p14 p15 p500 p532 p533 p534 p961 : Prop)
    (h16152 : (¬ p7))
    (h12247 : p7 ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p500) ∨ (¬ p532) ∨ (¬ p533) ∨ (¬ p534) ∨ (¬ p961)) : (¬ p14) ∨ (¬ p15) ∨ (¬ p500) ∨ (¬ p532) ∨ (¬ p533) ∨ (¬ p534) ∨ (¬ p961) := by
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
  have u2 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12247 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17386 (p7 p41 p195 p481 p798 p1385 : Prop)
    (h16152 : (¬ p7))
    (h12248 : p7 ∨ (¬ p41) ∨ (¬ p195) ∨ (¬ p481) ∨ (¬ p798) ∨ (¬ p1385)) : (¬ p41) ∨ (¬ p195) ∨ (¬ p481) ∨ (¬ p798) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p798 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12248 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17387 (p7 p45 p89 p132 p193 p258 p580 p633 p1136 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16259 : (¬ p1136))
    (h12249 : p7 ∨ (¬ p45) ∨ (¬ p89) ∨ (¬ p132) ∨ (¬ p193) ∨ (¬ p258) ∨ (¬ p580) ∨ (¬ p633) ∨ p1136) : (¬ p45) ∨ (¬ p89) ∨ (¬ p193) ∨ (¬ p258) ∨ (¬ p580) ∨ (¬ p633) := by
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
  have u3 : p258 := by
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
  have u7 : p132 := by
    exact h786
  have u8 : (¬ p1136) := by
    exact h16259
  rcases h12249 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u8 q8)

theorem step17388 (p7 p124 p135 p189 p258 p266 : Prop)
    (h16152 : (¬ p7))
    (h12251 : p7 ∨ (¬ p124) ∨ (¬ p135) ∨ (¬ p189) ∨ (¬ p258) ∨ (¬ p266)) : (¬ p124) ∨ (¬ p135) ∨ (¬ p189) ∨ (¬ p258) ∨ (¬ p266) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p124 := by
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
  have u3 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12251 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17390 (p535 p919 p1099 p1103 : Prop)
    (h2985 : p535)
    (h16230 : (¬ p919))
    (h12253 : (¬ p535) ∨ p919 ∨ (¬ p1099) ∨ p1103) : (¬ p1099) ∨ p1103 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1103) := fun hu => hn (Or.inr hu)
  have u2 : p535 := by
    exact h2985
  have u3 : (¬ p919) := by
    exact h16230
  rcases h12253 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (u1 q3)

theorem step17391 (p7 p15 p234 p500 p532 p961 p1330 p1366 : Prop)
    (h16152 : (¬ p7))
    (h12254 : p7 ∨ (¬ p15) ∨ (¬ p234) ∨ (¬ p500) ∨ (¬ p532) ∨ (¬ p961) ∨ (¬ p1330) ∨ (¬ p1366)) : (¬ p15) ∨ (¬ p234) ∨ (¬ p500) ∨ (¬ p532) ∨ (¬ p961) ∨ (¬ p1330) ∨ (¬ p1366) := by
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
  have u2 : p500 := by
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
  rcases h12254 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17393 (p7 p256 p344 p576 p686 p792 p814 p835 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h4535 : p792)
    (h12256 : p7 ∨ (¬ p256) ∨ (¬ p344) ∨ (¬ p576) ∨ p686 ∨ (¬ p792) ∨ (¬ p814) ∨ (¬ p835)) : (¬ p256) ∨ (¬ p344) ∨ (¬ p576) ∨ (¬ p814) ∨ (¬ p835) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p576 := by
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
  have u6 : (¬ p686) := by
    exact h16205
  have u7 : p792 := by
    exact h4535
  rcases h12256 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17394 (p7 p304 p348 p362 p726 p727 : Prop)
    (h16152 : (¬ p7))
    (h12257 : p7 ∨ (¬ p304) ∨ (¬ p348) ∨ (¬ p362) ∨ (¬ p726) ∨ (¬ p727)) : (¬ p304) ∨ (¬ p348) ∨ (¬ p362) ∨ (¬ p726) ∨ (¬ p727) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p727 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12257 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17396 (p7 p45 p129 p132 p256 p814 p1393 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h786 : p132)
    (h12260 : p7 ∨ (¬ p45) ∨ p129 ∨ (¬ p132) ∨ (¬ p256) ∨ (¬ p814) ∨ (¬ p1393)) : (¬ p45) ∨ (¬ p256) ∨ (¬ p814) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p132 := by
    exact h786
  rcases h12260 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17397 (p7 p45 p129 p304 p362 p427 p580 p633 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h2334 : p427)
    (h12261 : p7 ∨ (¬ p45) ∨ p129 ∨ (¬ p304) ∨ (¬ p362) ∨ (¬ p427) ∨ (¬ p580) ∨ (¬ p633)) : (¬ p45) ∨ (¬ p304) ∨ (¬ p362) ∨ (¬ p580) ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p427 := by
    exact h2334
  rcases h12261 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17398 (p7 p129 p189 p224 p343 p789 p790 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h1950 : p343)
    (h12262 : p7 ∨ p129 ∨ (¬ p189) ∨ (¬ p224) ∨ (¬ p343) ∨ (¬ p789) ∨ (¬ p790)) : (¬ p189) ∨ (¬ p224) ∨ (¬ p789) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p189 := by
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
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p343 := by
    exact h1950
  rcases h12262 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17399 (p7 p45 p1225 p1227 p1257 p1489 : Prop)
    (h16152 : (¬ p7))
    (h12263 : p7 ∨ (¬ p45) ∨ (¬ p1225) ∨ (¬ p1227) ∨ (¬ p1257) ∨ (¬ p1489)) : (¬ p45) ∨ (¬ p1225) ∨ (¬ p1227) ∨ (¬ p1257) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1257 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12263 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17400 (p7 p45 p125 p135 p265 p580 p601 : Prop)
    (h16152 : (¬ p7))
    (h12264 : p7 ∨ (¬ p45) ∨ (¬ p125) ∨ (¬ p135) ∨ (¬ p265) ∨ (¬ p580) ∨ (¬ p601)) : (¬ p45) ∨ (¬ p125) ∨ (¬ p135) ∨ (¬ p265) ∨ (¬ p580) ∨ (¬ p601) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
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
  have u4 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12264 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17401 (p7 p45 p382 p802 p819 p1286 p1392 : Prop)
    (h16152 : (¬ p7))
    (h12265 : p7 ∨ (¬ p45) ∨ (¬ p382) ∨ (¬ p802) ∨ (¬ p819) ∨ (¬ p1286) ∨ (¬ p1392)) : (¬ p45) ∨ (¬ p382) ∨ (¬ p802) ∨ (¬ p819) ∨ (¬ p1286) ∨ (¬ p1392) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p802 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p819 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1392 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12265 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17402 (p7 p8 p135 p189 p242 p283 p836 : Prop)
    (h16152 : (¬ p7))
    (h12266 : p7 ∨ (¬ p8) ∨ (¬ p135) ∨ (¬ p189) ∨ (¬ p242) ∨ (¬ p283) ∨ (¬ p836)) : (¬ p8) ∨ (¬ p135) ∨ (¬ p189) ∨ (¬ p242) ∨ (¬ p283) ∨ (¬ p836) := by
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
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12266 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17403 (p7 p101 p129 p189 p256 p288 p788 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h5066 : p788)
    (h12267 : p7 ∨ (¬ p101) ∨ p129 ∨ (¬ p189) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p788)) : (¬ p101) ∨ (¬ p189) ∨ (¬ p256) ∨ (¬ p288) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p788 := by
    exact h5066
  rcases h12267 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17404 (p7 p27 p101 p346 p640 p904 : Prop)
    (h16152 : (¬ p7))
    (h12271 : p7 ∨ (¬ p27) ∨ (¬ p101) ∨ (¬ p346) ∨ (¬ p640) ∨ (¬ p904)) : (¬ p27) ∨ (¬ p101) ∨ (¬ p346) ∨ (¬ p640) ∨ (¬ p904) := by
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
  have u2 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p640 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12271 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17405 (p7 p158 p230 p536 p726 p928 p1077 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6761 : p1139)
    (h12273 : p7 ∨ (¬ p158) ∨ p230 ∨ (¬ p536) ∨ (¬ p726) ∨ (¬ p928) ∨ (¬ p1077) ∨ (¬ p1139)) : (¬ p158) ∨ (¬ p536) ∨ (¬ p726) ∨ (¬ p928) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p928 := by
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
  have u7 : p1139 := by
    exact h6761
  rcases h12273 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step17406 (p7 p160 p401 p856 p1286 p1395 p1489 : Prop)
    (h16152 : (¬ p7))
    (h12274 : p7 ∨ (¬ p160) ∨ (¬ p401) ∨ (¬ p856) ∨ (¬ p1286) ∨ (¬ p1395) ∨ (¬ p1489)) : (¬ p160) ∨ (¬ p401) ∨ (¬ p856) ∨ (¬ p1286) ∨ (¬ p1395) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p401 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p856 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1395 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12274 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17407 (p7 p256 p343 p662 p791 p980 p1443 p1452 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16213 : (¬ p791))
    (h12275 : p7 ∨ (¬ p256) ∨ (¬ p343) ∨ (¬ p662) ∨ p791 ∨ (¬ p980) ∨ (¬ p1443) ∨ (¬ p1452)) : (¬ p256) ∨ (¬ p662) ∨ (¬ p980) ∨ (¬ p1443) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p662 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
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
  have u6 : p343 := by
    exact h1950
  have u7 : (¬ p791) := by
    exact h16213
  rcases h12275 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17408 (p7 p19 p40 p121 p1135 p1325 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h6744 : p1135)
    (h12276 : p7 ∨ (¬ p19) ∨ p40 ∨ (¬ p121) ∨ (¬ p1135) ∨ (¬ p1325) ∨ (¬ p1452)) : (¬ p19) ∨ (¬ p121) ∨ (¬ p1325) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
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
  have u5 : (¬ p40) := by
    exact h16150
  have u6 : p1135 := by
    exact h6744
  rcases h12276 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17409 (p7 p312 p346 p406 p419 p543 p680 : Prop)
    (h16152 : (¬ p7))
    (h12278 : p7 ∨ (¬ p312) ∨ (¬ p346) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p543) ∨ (¬ p680)) : (¬ p312) ∨ (¬ p346) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p543) ∨ (¬ p680) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p312 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p543 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12278 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17410 (p7 p127 p137 p167 p195 p288 p344 p560 p727 p769 : Prop)
    (h16152 : (¬ p7))
    (h12279 : p7 ∨ (¬ p127) ∨ (¬ p137) ∨ (¬ p167) ∨ (¬ p195) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p560) ∨ (¬ p727) ∨ (¬ p769)) : (¬ p127) ∨ (¬ p137) ∨ (¬ p167) ∨ (¬ p195) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p560) ∨ (¬ p727) ∨ (¬ p769) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p137 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p727 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h12279 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17411 (p7 p86 p237 p616 p1075 p1076 p1116 p1287 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16309 : (¬ p1324))
    (h12281 : p7 ∨ (¬ p86) ∨ (¬ p237) ∨ (¬ p616) ∨ (¬ p1075) ∨ (¬ p1076) ∨ (¬ p1116) ∨ (¬ p1287) ∨ p1324 ∨ (¬ p1325)) : (¬ p86) ∨ (¬ p237) ∨ (¬ p616) ∨ (¬ p1076) ∨ (¬ p1116) ∨ (¬ p1287) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p616 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p1075 := by
    exact h6478
  have u9 : (¬ p1324) := by
    exact h16309
  rcases h12281 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17414 (p7 p41 p63 p101 p141 p288 p788 p1136 : Prop)
    (h16152 : (¬ p7))
    (h5066 : p788)
    (h16259 : (¬ p1136))
    (h12284 : p7 ∨ (¬ p41) ∨ (¬ p63) ∨ (¬ p101) ∨ (¬ p141) ∨ (¬ p288) ∨ (¬ p788) ∨ p1136) : (¬ p41) ∨ (¬ p63) ∨ (¬ p101) ∨ (¬ p141) ∨ (¬ p288) := by
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
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p788 := by
    exact h5066
  have u7 : (¬ p1136) := by
    exact h16259
  rcases h12284 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u6)
  · exact False.elim (u7 q7)

theorem step17415 (p7 p41 p63 p102 p142 p1075 p1136 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16259 : (¬ p1136))
    (h12285 : p7 ∨ (¬ p41) ∨ (¬ p63) ∨ (¬ p102) ∨ (¬ p142) ∨ (¬ p1075) ∨ p1136) : (¬ p41) ∨ (¬ p63) ∨ (¬ p102) ∨ (¬ p142) := by
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
  have u2 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p1075 := by
    exact h6478
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h12285 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)

theorem step17416 (p7 p39 p69 p89 p790 p1385 : Prop)
    (h16152 : (¬ p7))
    (h12286 : p7 ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p89) ∨ (¬ p790) ∨ (¬ p1385)) : (¬ p39) ∨ (¬ p69) ∨ (¬ p89) ∨ (¬ p790) ∨ (¬ p1385) := by
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
  rcases h12286 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17417 (p7 p134 p195 p211 p1631 p1666 : Prop)
    (h16152 : (¬ p7))
    (h12287 : p7 ∨ (¬ p134) ∨ (¬ p195) ∨ (¬ p211) ∨ (¬ p1631) ∨ (¬ p1666)) : (¬ p134) ∨ (¬ p195) ∨ (¬ p211) ∨ (¬ p1631) ∨ (¬ p1666) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p211 := by
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
  rcases h12287 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17418 (p7 p63 p126 p434 p581 p685 p1136 : Prop)
    (h16152 : (¬ p7))
    (h3898 : p685)
    (h16259 : (¬ p1136))
    (h12289 : p7 ∨ (¬ p63) ∨ (¬ p126) ∨ (¬ p434) ∨ (¬ p581) ∨ (¬ p685) ∨ p1136) : (¬ p63) ∨ (¬ p126) ∨ (¬ p434) ∨ (¬ p581) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p126 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p685 := by
    exact h3898
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h12289 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)

theorem step17420 (p7 p14 p15 p167 p1136 p1256 p1708 : Prop)
    (h16152 : (¬ p7))
    (h16259 : (¬ p1136))
    (h10766 : p1708)
    (h12292 : p7 ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p167) ∨ p1136 ∨ (¬ p1256) ∨ (¬ p1708)) : (¬ p14) ∨ (¬ p15) ∨ (¬ p167) ∨ (¬ p1256) := by
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
  have u2 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p1136) := by
    exact h16259
  have u6 : p1708 := by
    exact h10766
  rcases h12292 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17421 (p7 p12 p41 p63 p163 p1136 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16259 : (¬ p1136))
    (h6761 : p1139)
    (h12293 : p7 ∨ (¬ p12) ∨ (¬ p41) ∨ (¬ p63) ∨ (¬ p163) ∨ p1136 ∨ (¬ p1139)) : (¬ p12) ∨ (¬ p41) ∨ (¬ p63) ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p1136) := by
    exact h16259
  have u6 : p1139 := by
    exact h6761
  rcases h12293 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step17422 (p7 p12 p45 p89 p169 p193 p928 p1136 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16259 : (¬ p1136))
    (h6761 : p1139)
    (h12294 : p7 ∨ (¬ p12) ∨ (¬ p45) ∨ (¬ p89) ∨ (¬ p169) ∨ (¬ p193) ∨ (¬ p928) ∨ p1136 ∨ (¬ p1139)) : (¬ p12) ∨ (¬ p45) ∨ (¬ p89) ∨ (¬ p169) ∨ (¬ p193) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p169 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p1136) := by
    exact h16259
  have u8 : p1139 := by
    exact h6761
  rcases h12294 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u7 q7)
  · exact False.elim (q8 u8)

theorem step17423 (p7 p45 p90 p186 p481 p796 : Prop)
    (h16152 : (¬ p7))
    (h12295 : p7 ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p186) ∨ (¬ p481) ∨ (¬ p796)) : (¬ p45) ∨ (¬ p90) ∨ (¬ p186) ∨ (¬ p481) ∨ (¬ p796) := by
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
  have u2 : p186 := by
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
  rcases h12295 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17424 (p7 p435 p790 p791 p996 p1022 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16213 : (¬ p791))
    (h6744 : p1135)
    (h12296 : p7 ∨ (¬ p435) ∨ (¬ p790) ∨ p791 ∨ (¬ p996) ∨ (¬ p1022) ∨ (¬ p1135)) : (¬ p435) ∨ (¬ p790) ∨ (¬ p996) ∨ (¬ p1022) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p791) := by
    exact h16213
  have u6 : p1135 := by
    exact h6744
  rcases h12296 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17425 (p7 p14 p44 p90 p193 p534 p735 p1015 p1385 : Prop)
    (h16152 : (¬ p7))
    (h12297 : p7 ∨ (¬ p14) ∨ (¬ p44) ∨ (¬ p90) ∨ (¬ p193) ∨ (¬ p534) ∨ (¬ p735) ∨ (¬ p1015) ∨ (¬ p1385)) : (¬ p14) ∨ (¬ p44) ∨ (¬ p90) ∨ (¬ p193) ∨ (¬ p534) ∨ (¬ p735) ∨ (¬ p1015) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p735 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12297 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17428 (p7 p45 p89 p193 p983 p1120 p1226 p1237 p1273 : Prop)
    (h16152 : (¬ p7))
    (h12302 : p7 ∨ (¬ p45) ∨ (¬ p89) ∨ (¬ p193) ∨ (¬ p983) ∨ (¬ p1120) ∨ (¬ p1226) ∨ (¬ p1237) ∨ (¬ p1273)) : (¬ p45) ∨ (¬ p89) ∨ (¬ p193) ∨ (¬ p983) ∨ (¬ p1120) ∨ (¬ p1226) ∨ (¬ p1237) ∨ (¬ p1273) := by
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
  have u3 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1120 := by
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
  have u7 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12302 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17429 (p7 p132 p581 p983 p1181 p1226 p1249 p1352 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16272 : (¬ p1181))
    (h12303 : p7 ∨ (¬ p132) ∨ (¬ p581) ∨ (¬ p983) ∨ p1181 ∨ (¬ p1226) ∨ (¬ p1249) ∨ (¬ p1352)) : (¬ p581) ∨ (¬ p983) ∨ (¬ p1226) ∨ (¬ p1249) ∨ (¬ p1352) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p983 := by
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
  have u6 : p132 := by
    exact h786
  have u7 : (¬ p1181) := by
    exact h16272
  rcases h12303 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17430 (p7 p45 p193 p288 p581 p791 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16213 : (¬ p791))
    (h6478 : p1075)
    (h12304 : p7 ∨ (¬ p45) ∨ (¬ p193) ∨ (¬ p288) ∨ (¬ p581) ∨ p791 ∨ (¬ p1075)) : (¬ p45) ∨ (¬ p193) ∨ (¬ p288) ∨ (¬ p581) := by
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
  have u2 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p791) := by
    exact h16213
  have u6 : p1075 := by
    exact h6478
  rcases h12304 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step17432 (p7 p143 p576 p1206 p1273 p1495 : Prop)
    (h16152 : (¬ p7))
    (h12307 : p7 ∨ (¬ p143) ∨ (¬ p576) ∨ (¬ p1206) ∨ (¬ p1273) ∨ (¬ p1495)) : (¬ p143) ∨ (¬ p576) ∨ (¬ p1206) ∨ (¬ p1273) ∨ (¬ p1495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1206 := by
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
  rcases h12307 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17433 (p7 p45 p89 p193 p495 p577 : Prop)
    (h16152 : (¬ p7))
    (h12308 : p7 ∨ (¬ p45) ∨ (¬ p89) ∨ (¬ p193) ∨ (¬ p495) ∨ (¬ p577)) : (¬ p45) ∨ (¬ p89) ∨ (¬ p193) ∨ (¬ p495) ∨ (¬ p577) := by
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
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12308 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17436 (p7 p161 p288 p581 p665 p1077 p1274 p1333 : Prop)
    (h16152 : (¬ p7))
    (h12311 : p7 ∨ (¬ p161) ∨ (¬ p288) ∨ (¬ p581) ∨ (¬ p665) ∨ (¬ p1077) ∨ (¬ p1274) ∨ (¬ p1333)) : (¬ p161) ∨ (¬ p288) ∨ (¬ p581) ∨ (¬ p665) ∨ (¬ p1077) ∨ (¬ p1274) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1274 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12311 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17437 (p7 p86 p161 p256 p288 p302 p343 p344 p1232 p1333 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h1950 : p343)
    (h12312 : p7 ∨ (¬ p86) ∨ (¬ p161) ∨ (¬ p256) ∨ (¬ p288) ∨ p302 ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p1232) ∨ (¬ p1333)) : (¬ p86) ∨ (¬ p161) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p1232) ∨ (¬ p1333) := by
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
  have u3 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p302) := by
    exact h16285
  have u9 : p343 := by
    exact h1950
  rcases h12312 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u8 q5)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step17438 (p7 p19 p40 p121 p124 p961 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h6478 : p1075)
    (h12315 : p7 ∨ (¬ p19) ∨ p40 ∨ (¬ p121) ∨ (¬ p124) ∨ (¬ p961) ∨ (¬ p1075)) : (¬ p19) ∨ (¬ p121) ∨ (¬ p124) ∨ (¬ p961) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p40) := by
    exact h16150
  have u6 : p1075 := by
    exact h6478
  rcases h12315 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17439 (p7 p70 p102 p127 p668 p897 p1077 p1099 : Prop)
    (h16152 : (¬ p7))
    (h12319 : p7 ∨ (¬ p70) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p668) ∨ (¬ p897) ∨ (¬ p1077) ∨ (¬ p1099)) : (¬ p70) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p668) ∨ (¬ p897) ∨ (¬ p1077) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12319 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17440 (p7 p15 p19 p102 p1077 p1136 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16259 : (¬ p1136))
    (h6761 : p1139)
    (h12320 : p7 ∨ (¬ p15) ∨ (¬ p19) ∨ (¬ p102) ∨ (¬ p1077) ∨ p1136 ∨ (¬ p1139)) : (¬ p15) ∨ (¬ p19) ∨ (¬ p102) ∨ (¬ p1077) := by
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
  have u2 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p1136) := by
    exact h16259
  have u6 : p1139 := by
    exact h6761
  rcases h12320 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step17441 (p7 p41 p102 p127 p187 p230 p1077 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6761 : p1139)
    (h12321 : p7 ∨ (¬ p41) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p187) ∨ p230 ∨ (¬ p1077) ∨ (¬ p1139)) : (¬ p41) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p187) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p102 := by
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
  have u4 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p1139 := by
    exact h6761
  rcases h12321 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step17443 (p7 p237 p789 p791 p839 p980 p1139 p1333 : Prop)
    (h16152 : (¬ p7))
    (h16213 : (¬ p791))
    (h6761 : p1139)
    (h12326 : p7 ∨ (¬ p237) ∨ (¬ p789) ∨ p791 ∨ (¬ p839) ∨ (¬ p980) ∨ (¬ p1139) ∨ (¬ p1333)) : (¬ p237) ∨ (¬ p789) ∨ (¬ p839) ∨ (¬ p980) ∨ (¬ p1333) := by
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
  have u2 : p839 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p791) := by
    exact h16213
  have u7 : p1139 := by
    exact h6761
  rcases h12326 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step17444 (p7 p86 p256 p288 p616 p665 p1077 p1287 : Prop)
    (h16152 : (¬ p7))
    (h12327 : p7 ∨ (¬ p86) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p616) ∨ (¬ p665) ∨ (¬ p1077) ∨ (¬ p1287)) : (¬ p86) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p616) ∨ (¬ p665) ∨ (¬ p1077) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12327 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17445 (p7 p256 p288 p344 p382 p821 p906 p1286 : Prop)
    (h16152 : (¬ p7))
    (h12328 : p7 ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p382) ∨ (¬ p821) ∨ (¬ p906) ∨ (¬ p1286)) : (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p382) ∨ (¬ p821) ∨ (¬ p906) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p821 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p906 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12328 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17446 (p7 p237 p343 p344 p537 p726 p791 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16213 : (¬ p791))
    (h12329 : p7 ∨ (¬ p237) ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p537) ∨ (¬ p726) ∨ p791) : (¬ p237) ∨ (¬ p344) ∨ (¬ p537) ∨ (¬ p726) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p343 := by
    exact h1950
  have u6 : (¬ p791) := by
    exact h16213
  rcases h12329 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step17449 (p7 p287 p301 p362 p658 p1075 p1076 p1116 : Prop)
    (h16152 : (¬ p7))
    (h16199 : (¬ p658))
    (h6478 : p1075)
    (h12332 : p7 ∨ (¬ p287) ∨ (¬ p301) ∨ (¬ p362) ∨ p658 ∨ (¬ p1075) ∨ (¬ p1076) ∨ (¬ p1116)) : (¬ p287) ∨ (¬ p301) ∨ (¬ p362) ∨ (¬ p1076) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p362 := by
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
  have u6 : (¬ p658) := by
    exact h16199
  have u7 : p1075 := by
    exact h6478
  rcases h12332 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17450 (p7 p63 p928 p1075 p1076 p1116 p1136 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16259 : (¬ p1136))
    (h12333 : p7 ∨ (¬ p63) ∨ (¬ p928) ∨ (¬ p1075) ∨ (¬ p1076) ∨ (¬ p1116) ∨ p1136) : (¬ p63) ∨ (¬ p928) ∨ (¬ p1076) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p1075 := by
    exact h6478
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h12333 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step17451 (p7 p302 p346 p419 p690 p713 p1075 p1366 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h6478 : p1075)
    (h12334 : p7 ∨ p302 ∨ (¬ p346) ∨ (¬ p419) ∨ (¬ p690) ∨ (¬ p713) ∨ (¬ p1075) ∨ (¬ p1366)) : (¬ p346) ∨ (¬ p419) ∨ (¬ p690) ∨ (¬ p713) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p713 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p302) := by
    exact h16285
  have u7 : p1075 := by
    exact h6478
  rcases h12334 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step17452 (p7 p347 p438 p736 p897 p1562 : Prop)
    (h16152 : (¬ p7))
    (h12335 : p7 ∨ (¬ p347) ∨ (¬ p438) ∨ (¬ p736) ∨ (¬ p897) ∨ (¬ p1562)) : (¬ p347) ∨ (¬ p438) ∨ (¬ p736) ∨ (¬ p897) ∨ (¬ p1562) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p736 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12335 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17453 (p7 p86 p121 p142 p193 p347 p381 p897 p1099 : Prop)
    (h16152 : (¬ p7))
    (h12336 : p7 ∨ (¬ p86) ∨ (¬ p121) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p347) ∨ (¬ p381) ∨ (¬ p897) ∨ (¬ p1099)) : (¬ p86) ∨ (¬ p121) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p347) ∨ (¬ p381) ∨ (¬ p897) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p381 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12336 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17454 (p7 p14 p18 p107 p139 p258 : Prop)
    (h16152 : (¬ p7))
    (h12337 : p7 ∨ (¬ p14) ∨ (¬ p18) ∨ (¬ p107) ∨ (¬ p139) ∨ (¬ p258)) : (¬ p14) ∨ (¬ p18) ∨ (¬ p107) ∨ (¬ p139) ∨ (¬ p258) := by
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
  have u3 : p139 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12337 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17455 (p7 p14 p18 p107 p209 p304 : Prop)
    (h16152 : (¬ p7))
    (h12339 : p7 ∨ (¬ p14) ∨ (¬ p18) ∨ (¬ p107) ∨ (¬ p209) ∨ (¬ p304)) : (¬ p14) ∨ (¬ p18) ∨ (¬ p107) ∨ (¬ p209) ∨ (¬ p304) := by
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
  have u3 : p209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12339 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17457 (p7 p499 p633 p665 p1077 p1226 p1237 p1333 : Prop)
    (h16152 : (¬ p7))
    (h12342 : p7 ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p665) ∨ (¬ p1077) ∨ (¬ p1226) ∨ (¬ p1237) ∨ (¬ p1333)) : (¬ p499) ∨ (¬ p633) ∨ (¬ p665) ∨ (¬ p1077) ∨ (¬ p1226) ∨ (¬ p1237) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1077 := by
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
  have u6 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12342 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17458 (p7 p41 p63 p424 p996 p1135 p1136 : Prop)
    (h16152 : (¬ p7))
    (h6744 : p1135)
    (h16259 : (¬ p1136))
    (h12343 : p7 ∨ (¬ p41) ∨ (¬ p63) ∨ (¬ p424) ∨ (¬ p996) ∨ (¬ p1135) ∨ p1136) : (¬ p41) ∨ (¬ p63) ∨ (¬ p424) ∨ (¬ p996) := by
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
  have u5 : p1135 := by
    exact h6744
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h12343 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)

theorem step17460 (p7 p800 p1015 p1187 p1371 p1712 : Prop)
    (h16152 : (¬ p7))
    (h12346 : p7 ∨ (¬ p800) ∨ (¬ p1015) ∨ (¬ p1187) ∨ (¬ p1371) ∨ (¬ p1712)) : (¬ p800) ∨ (¬ p1015) ∨ (¬ p1187) ∨ (¬ p1371) ∨ (¬ p1712) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p800 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1371 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1712 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12346 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17461 (p7 p344 p382 p499 p545 p621 p633 p996 : Prop)
    (h16152 : (¬ p7))
    (h12347 : p7 ∨ (¬ p344) ∨ (¬ p382) ∨ (¬ p499) ∨ (¬ p545) ∨ (¬ p621) ∨ (¬ p633) ∨ (¬ p996)) : (¬ p344) ∨ (¬ p382) ∨ (¬ p499) ∨ (¬ p545) ∨ (¬ p621) ∨ (¬ p633) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p621 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12347 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17462 (p7 p17 p123 p237 p666 p1116 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h8348 : p1386)
    (h12348 : p7 ∨ (¬ p17) ∨ p123 ∨ (¬ p237) ∨ (¬ p666) ∨ (¬ p1116) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p17) ∨ (¬ p237) ∨ (¬ p666) ∨ (¬ p1116) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p123) := by
    exact h16186
  have u7 : p1386 := by
    exact h8348
  rcases h12348 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step17463 (p7 p46 p169 p189 p229 p237 : Prop)
    (h16152 : (¬ p7))
    (h12349 : p7 ∨ (¬ p46) ∨ (¬ p169) ∨ (¬ p189) ∨ (¬ p229) ∨ (¬ p237)) : (¬ p46) ∨ (¬ p169) ∨ (¬ p189) ∨ (¬ p229) ∨ (¬ p237) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p46 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p169 := by
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
  have u4 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12349 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17465 (p7 p17 p41 p42 p123 p237 p918 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16186 : (¬ p123))
    (h12353 : p7 ∨ (¬ p17) ∨ (¬ p41) ∨ (¬ p42) ∨ p123 ∨ (¬ p237) ∨ (¬ p918)) : (¬ p17) ∨ (¬ p41) ∨ (¬ p237) ∨ (¬ p918) := by
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
  have u2 : p237 := by
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
  have u6 : (¬ p123) := by
    exact h16186
  rcases h12353 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17466 (p7 p17 p138 p186 p422 p1140 : Prop)
    (h16152 : (¬ p7))
    (h12354 : p7 ∨ (¬ p17) ∨ (¬ p138) ∨ (¬ p186) ∨ (¬ p422) ∨ (¬ p1140)) : (¬ p17) ∨ (¬ p138) ∨ (¬ p186) ∨ (¬ p422) ∨ (¬ p1140) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12354 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17469 (p7 p138 p576 p1225 p1227 p1252 p1489 : Prop)
    (h16152 : (¬ p7))
    (h12357 : p7 ∨ (¬ p138) ∨ (¬ p576) ∨ (¬ p1225) ∨ (¬ p1227) ∨ (¬ p1252) ∨ (¬ p1489)) : (¬ p138) ∨ (¬ p576) ∨ (¬ p1225) ∨ (¬ p1227) ∨ (¬ p1252) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1252 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12357 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17470 (p5 p7 p434 p499 p601 p1159 p1330 p1465 : Prop)
    (h16152 : (¬ p7))
    (h12358 : (¬ p5) ∨ p7 ∨ (¬ p434) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1159) ∨ (¬ p1330) ∨ (¬ p1465)) : (¬ p5) ∨ (¬ p434) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1159) ∨ (¬ p1330) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p434 := by
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
  have u4 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12358 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17471 (p7 p8 p534 p653 p657 p769 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16194 : (¬ p653))
    (h6744 : p1135)
    (h12359 : p7 ∨ (¬ p8) ∨ (¬ p534) ∨ p653 ∨ (¬ p657) ∨ (¬ p769) ∨ (¬ p1135)) : (¬ p8) ∨ (¬ p534) ∨ (¬ p657) ∨ (¬ p769) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p653) := by
    exact h16194
  have u6 : p1135 := by
    exact h6744
  rcases h12359 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17472 (p7 p224 p343 p406 p534 p653 p680 p769 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16194 : (¬ p653))
    (h12360 : p7 ∨ (¬ p224) ∨ (¬ p343) ∨ (¬ p406) ∨ (¬ p534) ∨ p653 ∨ (¬ p680) ∨ (¬ p769)) : (¬ p224) ∨ (¬ p406) ∨ (¬ p534) ∨ (¬ p680) ∨ (¬ p769) := by
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
  have u2 : p534 := by
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
  have u6 : p343 := by
    exact h1950
  have u7 : (¬ p653) := by
    exact h16194
  rcases h12360 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u7 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17474 (p7 p387 p499 p601 p1136 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16259 : (¬ p1136))
    (h8348 : p1386)
    (h12362 : p7 ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ p1136 ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p387 := by
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
  have u3 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p1136) := by
    exact h16259
  have u6 : p1386 := by
    exact h8348
  rcases h12362 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17475 (p7 p657 p904 p1096 p1136 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16259 : (¬ p1136))
    (h8348 : p1386)
    (h12363 : p7 ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1096) ∨ p1136 ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p657) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p657 := by
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
  have u3 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p1136) := by
    exact h16259
  have u6 : p1386 := by
    exact h8348
  rcases h12363 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17476 (p7 p17 p237 p286 p578 p636 : Prop)
    (h16152 : (¬ p7))
    (h12364 : p7 ∨ (¬ p17) ∨ (¬ p237) ∨ (¬ p286) ∨ (¬ p578) ∨ (¬ p636)) : (¬ p17) ∨ (¬ p237) ∨ (¬ p286) ∨ (¬ p578) ∨ (¬ p636) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p578 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12364 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17477 (p7 p344 p499 p633 p657 p1135 p1136 : Prop)
    (h16152 : (¬ p7))
    (h6744 : p1135)
    (h16259 : (¬ p1136))
    (h12365 : p7 ∨ (¬ p344) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p657) ∨ (¬ p1135) ∨ p1136) : (¬ p344) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p657) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
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
  have u3 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p1135 := by
    exact h6744
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h12365 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)

theorem step17478 (p7 p17 p123 p224 p343 p789 p790 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h1950 : p343)
    (h12366 : p7 ∨ (¬ p17) ∨ p123 ∨ (¬ p224) ∨ (¬ p343) ∨ (¬ p789) ∨ (¬ p790)) : (¬ p17) ∨ (¬ p224) ∨ (¬ p789) ∨ (¬ p790) := by
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
  have u5 : (¬ p123) := by
    exact h16186
  have u6 : p343 := by
    exact h1950
  rcases h12366 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17479 (p7 p45 p90 p406 p797 p820 p858 : Prop)
    (h16152 : (¬ p7))
    (h12367 : p7 ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p406) ∨ (¬ p797) ∨ (¬ p820) ∨ (¬ p858)) : (¬ p45) ∨ (¬ p90) ∨ (¬ p406) ∨ (¬ p797) ∨ (¬ p820) ∨ (¬ p858) := by
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
  rcases h12367 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17480 (p7 p17 p420 p518 p578 p790 : Prop)
    (h16152 : (¬ p7))
    (h12369 : p7 ∨ (¬ p17) ∨ (¬ p420) ∨ (¬ p518) ∨ (¬ p578) ∨ (¬ p790)) : (¬ p17) ∨ (¬ p420) ∨ (¬ p518) ∨ (¬ p578) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p518 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p578 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12369 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17482 (p7 p17 p230 p237 p286 p581 p1077 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6761 : p1139)
    (h12373 : p7 ∨ (¬ p17) ∨ p230 ∨ (¬ p237) ∨ (¬ p286) ∨ (¬ p581) ∨ (¬ p1077) ∨ (¬ p1139)) : (¬ p17) ∨ (¬ p237) ∨ (¬ p286) ∨ (¬ p581) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p581 := by
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
  have u7 : p1139 := by
    exact h6761
  rcases h12373 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step17483 (p7 p17 p123 p237 p657 p840 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h6744 : p1135)
    (h12374 : p7 ∨ (¬ p17) ∨ p123 ∨ (¬ p237) ∨ (¬ p657) ∨ (¬ p840) ∨ (¬ p1135)) : (¬ p17) ∨ (¬ p237) ∨ (¬ p657) ∨ (¬ p840) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p123) := by
    exact h16186
  have u6 : p1135 := by
    exact h6744
  rcases h12374 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17484 (p7 p17 p138 p237 p545 p797 p840 p858 p996 : Prop)
    (h16152 : (¬ p7))
    (h12375 : p7 ∨ (¬ p17) ∨ (¬ p138) ∨ (¬ p237) ∨ (¬ p545) ∨ (¬ p797) ∨ (¬ p840) ∨ (¬ p858) ∨ (¬ p996)) : (¬ p17) ∨ (¬ p138) ∨ (¬ p237) ∨ (¬ p545) ∨ (¬ p797) ∨ (¬ p840) ∨ (¬ p858) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p797 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12375 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17485 (p7 p69 p124 p419 p496 p665 p1077 p1187 : Prop)
    (h16152 : (¬ p7))
    (h12377 : p7 ∨ (¬ p69) ∨ (¬ p124) ∨ (¬ p419) ∨ (¬ p496) ∨ (¬ p665) ∨ (¬ p1077) ∨ (¬ p1187)) : (¬ p69) ∨ (¬ p124) ∨ (¬ p419) ∨ (¬ p496) ∨ (¬ p665) ∨ (¬ p1077) ∨ (¬ p1187) := by
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
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12377 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17486 (p7 p138 p192 p556 p576 p710 p904 p927 : Prop)
    (h16152 : (¬ p7))
    (h12378 : p7 ∨ (¬ p138) ∨ (¬ p192) ∨ (¬ p556) ∨ (¬ p576) ∨ (¬ p710) ∨ (¬ p904) ∨ (¬ p927)) : (¬ p138) ∨ (¬ p192) ∨ (¬ p556) ∨ (¬ p576) ∨ (¬ p710) ∨ (¬ p904) ∨ (¬ p927) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p556 := by
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
  rcases h12378 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17487 (p7 p237 p286 p668 p814 p835 p1077 : Prop)
    (h16152 : (¬ p7))
    (h12379 : p7 ∨ (¬ p237) ∨ (¬ p286) ∨ (¬ p668) ∨ (¬ p814) ∨ (¬ p835) ∨ (¬ p1077)) : (¬ p237) ∨ (¬ p286) ∨ (¬ p668) ∨ (¬ p814) ∨ (¬ p835) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p668 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12379 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17489 (p7 p124 p161 p496 p1035 p1044 p1077 p1232 : Prop)
    (h16152 : (¬ p7))
    (h12381 : p7 ∨ (¬ p124) ∨ (¬ p161) ∨ (¬ p496) ∨ (¬ p1035) ∨ (¬ p1044) ∨ (¬ p1077) ∨ (¬ p1232)) : (¬ p124) ∨ (¬ p161) ∨ (¬ p496) ∨ (¬ p1035) ∨ (¬ p1044) ∨ (¬ p1077) ∨ (¬ p1232) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12381 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17491 (p2 p5 p7 p419 p1075 p1076 p1095 p1096 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16309 : (¬ p1324))
    (h12384 : (¬ p2) ∨ (¬ p5) ∨ p7 ∨ (¬ p419) ∨ (¬ p1075) ∨ (¬ p1076) ∨ (¬ p1095) ∨ (¬ p1096) ∨ p1324 ∨ (¬ p1325)) : (¬ p2) ∨ (¬ p5) ∨ (¬ p419) ∨ (¬ p1076) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1325) := by
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
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p1075 := by
    exact h6478
  have u9 : (¬ p1324) := by
    exact h16309
  rcases h12384 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u9 q8)
  · exact False.elim (q9 u6)

theorem step17492 (p7 p495 p1075 p1076 p1095 p1096 p1160 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16265 : (¬ p1160))
    (h12385 : p7 ∨ (¬ p495) ∨ (¬ p1075) ∨ (¬ p1076) ∨ (¬ p1095) ∨ (¬ p1096) ∨ p1160) : (¬ p495) ∨ (¬ p1076) ∨ (¬ p1095) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1076 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p1075 := by
    exact h6478
  have u6 : (¬ p1160) := by
    exact h16265
  rcases h12385 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step17493 (p1 p7 p110 p499 p640 p657 p734 p1076 p1095 p1135 p1136 p1366 : Prop)
    (h16152 : (¬ p7))
    (h6744 : p1135)
    (h16259 : (¬ p1136))
    (h12386 : (¬ p1) ∨ p7 ∨ (¬ p110) ∨ (¬ p499) ∨ (¬ p640) ∨ (¬ p657) ∨ (¬ p734) ∨ (¬ p1076) ∨ (¬ p1095) ∨ (¬ p1135) ∨ p1136 ∨ (¬ p1366)) : (¬ p1) ∨ (¬ p110) ∨ (¬ p499) ∨ (¬ p640) ∨ (¬ p657) ∨ (¬ p734) ∨ (¬ p1076) ∨ (¬ p1095) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p640 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p1135 := by
    exact h6744
  have u11 : (¬ p1136) := by
    exact h16259
  rcases h12386 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u0)
  · exact False.elim (u9 q1)
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

theorem step17494 (p7 p303 p347 p666 p710 p1095 p1102 : Prop)
    (h16152 : (¬ p7))
    (h12388 : p7 ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p666) ∨ (¬ p710) ∨ (¬ p1095) ∨ (¬ p1102)) : (¬ p303) ∨ (¬ p347) ∨ (¬ p666) ∨ (¬ p710) ∨ (¬ p1095) ∨ (¬ p1102) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12388 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17495 (p7 p368 p658 p687 p898 p1075 p1076 p1095 p1545 : Prop)
    (h16152 : (¬ p7))
    (h16199 : (¬ p658))
    (h6478 : p1075)
    (h12389 : p7 ∨ (¬ p368) ∨ p658 ∨ (¬ p687) ∨ (¬ p898) ∨ (¬ p1075) ∨ (¬ p1076) ∨ (¬ p1095) ∨ (¬ p1545)) : (¬ p368) ∨ (¬ p687) ∨ (¬ p898) ∨ (¬ p1076) ∨ (¬ p1095) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p898 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p658) := by
    exact h16199
  have u8 : p1075 := by
    exact h6478
  rcases h12389 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step17496 (p7 p387 p438 p595 p1135 p1136 p1542 : Prop)
    (h16152 : (¬ p7))
    (h6744 : p1135)
    (h16259 : (¬ p1136))
    (h12390 : p7 ∨ (¬ p387) ∨ (¬ p438) ∨ (¬ p595) ∨ (¬ p1135) ∨ p1136 ∨ (¬ p1542)) : (¬ p387) ∨ (¬ p438) ∨ (¬ p595) ∨ (¬ p1542) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
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
  rcases h12390 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step17497 (p7 p41 p42 p434 p499 p601 p1136 p1249 p1330 p1489 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16259 : (¬ p1136))
    (h12392 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p434) ∨ (¬ p499) ∨ (¬ p601) ∨ p1136 ∨ (¬ p1249) ∨ (¬ p1330) ∨ (¬ p1489)) : (¬ p41) ∨ (¬ p434) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1249) ∨ (¬ p1330) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p434 := by
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
  have u4 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p42 := by
    exact h132
  have u9 : (¬ p1136) := by
    exact h16259
  rcases h12392 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u9 q6)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step17498 (p7 p362 p420 p498 p640 p1075 p1076 p1095 p1136 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16259 : (¬ p1136))
    (h12393 : p7 ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p498) ∨ (¬ p640) ∨ (¬ p1075) ∨ (¬ p1076) ∨ (¬ p1095) ∨ p1136) : (¬ p362) ∨ (¬ p420) ∨ (¬ p498) ∨ (¬ p640) ∨ (¬ p1076) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p640 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : p1075 := by
    exact h6478
  have u8 : (¬ p1136) := by
    exact h16259
  rcases h12393 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u8 q8)

theorem step17499 (p5 p7 p728 p904 p1096 p1159 p1330 p1465 : Prop)
    (h16152 : (¬ p7))
    (h12394 : (¬ p5) ∨ p7 ∨ (¬ p728) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1159) ∨ (¬ p1330) ∨ (¬ p1465)) : (¬ p5) ∨ (¬ p728) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1159) ∨ (¬ p1330) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p728 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12394 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17500 (p7 p430 p734 p897 p1075 p1076 p1095 : Prop)
    (h16152 : (¬ p7))
    (h16180 : (¬ p430))
    (h6478 : p1075)
    (h12396 : p7 ∨ p430 ∨ (¬ p734) ∨ (¬ p897) ∨ (¬ p1075) ∨ (¬ p1076) ∨ (¬ p1095)) : (¬ p734) ∨ (¬ p897) ∨ (¬ p1076) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p430) := by
    exact h16180
  have u6 : p1075 := by
    exact h6478
  rcases h12396 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17501 (p2 p5 p7 p431 p435 p657 p904 p1096 : Prop)
    (h16152 : (¬ p7))
    (h12397 : (¬ p2) ∨ (¬ p5) ∨ p7 ∨ (¬ p431) ∨ (¬ p435) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1096)) : (¬ p2) ∨ (¬ p5) ∨ (¬ p431) ∨ (¬ p435) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1096) := by
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
  have u2 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p435 := by
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
  rcases h12397 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17502 (p7 p126 p237 p427 p581 p791 p918 : Prop)
    (h16152 : (¬ p7))
    (h2334 : p427)
    (h16213 : (¬ p791))
    (h12398 : p7 ∨ (¬ p126) ∨ (¬ p237) ∨ (¬ p427) ∨ (¬ p581) ∨ p791 ∨ (¬ p918)) : (¬ p126) ∨ (¬ p237) ∨ (¬ p581) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p427 := by
    exact h2334
  have u6 : (¬ p791) := by
    exact h16213
  rcases h12398 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step17503 (p7 p288 p301 p499 p601 p1075 p1136 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16259 : (¬ p1136))
    (h12399 : p7 ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1075) ∨ p1136) : (¬ p288) ∨ (¬ p301) ∨ (¬ p499) ∨ (¬ p601) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p301 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p1075 := by
    exact h6478
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h12399 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)

theorem step17504 (p7 p63 p288 p301 p580 p601 p1075 p1136 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16259 : (¬ p1136))
    (h12400 : p7 ∨ (¬ p63) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p580) ∨ (¬ p601) ∨ (¬ p1075) ∨ p1136) : (¬ p63) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p580) ∨ (¬ p601) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
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
  have u3 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p1075 := by
    exact h6478
  have u7 : (¬ p1136) := by
    exact h16259
  rcases h12400 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u6)
  · exact False.elim (u7 q7)

theorem step17505 (p7 p426 p710 p792 p918 p1061 p1115 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h4535 : p792)
    (h12401 : p7 ∨ p426 ∨ (¬ p710) ∨ (¬ p792) ∨ (¬ p918) ∨ (¬ p1061) ∨ (¬ p1115)) : (¬ p710) ∨ (¬ p918) ∨ (¬ p1061) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p426) := by
    exact h16178
  have u6 : p792 := by
    exact h4535
  rcases h12401 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17506 (p2 p5 p7 p419 p434 p499 p601 p1334 : Prop)
    (h16152 : (¬ p7))
    (h12402 : (¬ p2) ∨ (¬ p5) ∨ p7 ∨ (¬ p419) ∨ (¬ p434) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1334)) : (¬ p2) ∨ (¬ p5) ∨ (¬ p419) ∨ (¬ p434) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1334) := by
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
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12402 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17507 (p7 p41 p42 p310 p658 p918 p1061 p1115 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16199 : (¬ p658))
    (h12404 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p310) ∨ p658 ∨ (¬ p918) ∨ (¬ p1061) ∨ (¬ p1115)) : (¬ p41) ∨ (¬ p310) ∨ (¬ p918) ∨ (¬ p1061) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
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
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p658) := by
    exact h16199
  rcases h12404 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17508 (p7 p15 p49 p84 p256 p302 p419 p616 p1189 p1386 p1443 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h8348 : p1386)
    (h12405 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p256) ∨ p302 ∨ (¬ p419) ∨ (¬ p616) ∨ (¬ p1189) ∨ (¬ p1386) ∨ (¬ p1443) ∨ (¬ p1452)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p616) ∨ (¬ p1189) ∨ (¬ p1443) ∨ (¬ p1452) := by
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
  have u3 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p302) := by
    exact h16285
  have u11 : p1386 := by
    exact h8348
  rcases h12405 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u10 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u11)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step17510 (p7 p545 p663 p840 p996 p1115 : Prop)
    (h16152 : (¬ p7))
    (h12407 : p7 ∨ (¬ p545) ∨ (¬ p663) ∨ (¬ p840) ∨ (¬ p996) ∨ (¬ p1115)) : (¬ p545) ∨ (¬ p663) ∨ (¬ p840) ∨ (¬ p996) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p663 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12407 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17511 (p2 p7 p194 p256 p435 p1335 p1443 p1452 : Prop)
    (h16152 : (¬ p7))
    (h12409 : (¬ p2) ∨ p7 ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p435) ∨ (¬ p1335) ∨ (¬ p1443) ∨ (¬ p1452)) : (¬ p2) ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p435) ∨ (¬ p1335) ∨ (¬ p1443) ∨ (¬ p1452) := by
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
  have u2 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12409 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17512 (p7 p88 p194 p477 p545 p690 p840 p927 p1061 p1098 p1115 p1366 : Prop)
    (h16152 : (¬ p7))
    (h12410 : p7 ∨ (¬ p88) ∨ (¬ p194) ∨ (¬ p477) ∨ (¬ p545) ∨ (¬ p690) ∨ (¬ p840) ∨ (¬ p927) ∨ (¬ p1061) ∨ (¬ p1098) ∨ (¬ p1115) ∨ (¬ p1366)) : (¬ p88) ∨ (¬ p194) ∨ (¬ p477) ∨ (¬ p545) ∨ (¬ p690) ∨ (¬ p840) ∨ (¬ p927) ∨ (¬ p1061) ∨ (¬ p1098) ∨ (¬ p1115) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p477 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1098 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : (¬ p7) := by
    exact h16152
  rcases h12410 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
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

theorem step17514 (p2 p7 p101 p124 p211 p326 : Prop)
    (h16152 : (¬ p7))
    (h12412 : (¬ p2) ∨ p7 ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p211) ∨ (¬ p326)) : (¬ p2) ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p211) ∨ (¬ p326) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
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
  have u3 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12412 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17515 (p7 p11 p15 p49 p110 p227 p288 p421 p580 p880 p1099 : Prop)
    (h16152 : (¬ p7))
    (h12414 : p7 ∨ (¬ p11) ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p110) ∨ (¬ p227) ∨ (¬ p288) ∨ (¬ p421) ∨ (¬ p580) ∨ (¬ p880) ∨ (¬ p1099)) : (¬ p11) ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p110) ∨ (¬ p227) ∨ (¬ p288) ∨ (¬ p421) ∨ (¬ p580) ∨ (¬ p880) ∨ (¬ p1099) := by
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
  have u2 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h12414 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step17516 (p2 p5 p7 p63 p435 p1273 p1335 p1508 : Prop)
    (h16152 : (¬ p7))
    (h12415 : (¬ p2) ∨ (¬ p5) ∨ p7 ∨ (¬ p63) ∨ (¬ p435) ∨ (¬ p1273) ∨ (¬ p1335) ∨ (¬ p1508)) : (¬ p2) ∨ (¬ p5) ∨ (¬ p63) ∨ (¬ p435) ∨ (¬ p1273) ∨ (¬ p1335) ∨ (¬ p1508) := by
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
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12415 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17517 (p7 p41 p42 p89 p237 p922 p1074 p1116 p1136 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16259 : (¬ p1136))
    (h12416 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ (¬ p89) ∨ (¬ p237) ∨ (¬ p922) ∨ (¬ p1074) ∨ (¬ p1116) ∨ p1136) : (¬ p41) ∨ (¬ p89) ∨ (¬ p237) ∨ (¬ p922) ∨ (¬ p1074) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p922 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : p42 := by
    exact h132
  have u8 : (¬ p1136) := by
    exact h16259
  rcases h12416 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u8 q8)

theorem step17518 (p7 p983 p1095 p1096 p1135 p1136 p1325 : Prop)
    (h16152 : (¬ p7))
    (h6744 : p1135)
    (h16259 : (¬ p1136))
    (h12417 : p7 ∨ (¬ p983) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1135) ∨ p1136 ∨ (¬ p1325)) : (¬ p983) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1096 := by
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
  rcases h12417 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step17519 (p7 p110 p346 p557 p680 p687 p734 : Prop)
    (h16152 : (¬ p7))
    (h12418 : p7 ∨ (¬ p110) ∨ (¬ p346) ∨ (¬ p557) ∨ (¬ p680) ∨ (¬ p687) ∨ (¬ p734)) : (¬ p110) ∨ (¬ p346) ∨ (¬ p557) ∨ (¬ p680) ∨ (¬ p687) ∨ (¬ p734) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12418 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17520 (p7 p47 p87 p189 p419 p1022 p1187 p1334 p1393 : Prop)
    (h16152 : (¬ p7))
    (h12420 : p7 ∨ (¬ p47) ∨ (¬ p87) ∨ (¬ p189) ∨ (¬ p419) ∨ (¬ p1022) ∨ (¬ p1187) ∨ (¬ p1334) ∨ (¬ p1393)) : (¬ p47) ∨ (¬ p87) ∨ (¬ p189) ∨ (¬ p419) ∨ (¬ p1022) ∨ (¬ p1187) ∨ (¬ p1334) ∨ (¬ p1393) := by
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
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12420 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17521 (p7 p279 p302 p419 p814 p1015 p1366 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16285 : (¬ p302))
    (h12421 : p7 ∨ (¬ p279) ∨ p302 ∨ (¬ p419) ∨ (¬ p814) ∨ (¬ p1015) ∨ (¬ p1366)) : (¬ p419) ∨ (¬ p814) ∨ (¬ p1015) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p279 := by
    exact h1444
  have u6 : (¬ p302) := by
    exact h16285
  rcases h12421 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17522 (p7 p230 p262 p362 p387 p581 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h8348 : p1386)
    (h12422 : p7 ∨ p230 ∨ (¬ p262) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p581) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p262) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p581) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p581 := by
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
  rcases h12422 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step17523 (p7 p87 p188 p556 p710 p840 p928 : Prop)
    (h16152 : (¬ p7))
    (h12423 : p7 ∨ (¬ p87) ∨ (¬ p188) ∨ (¬ p556) ∨ (¬ p710) ∨ (¬ p840) ∨ (¬ p928)) : (¬ p87) ∨ (¬ p188) ∨ (¬ p556) ∨ (¬ p710) ∨ (¬ p840) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12423 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17524 (p7 p110 p309 p544 p897 p1055 p1095 : Prop)
    (h16152 : (¬ p7))
    (h12424 : p7 ∨ (¬ p110) ∨ (¬ p309) ∨ (¬ p544) ∨ (¬ p897) ∨ (¬ p1055) ∨ (¬ p1095)) : (¬ p110) ∨ (¬ p309) ∨ (¬ p544) ∨ (¬ p897) ∨ (¬ p1055) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12424 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17525 (p7 p69 p134 p163 p229 p257 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h7053 : p1184)
    (h12425 : p7 ∨ (¬ p69) ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p229) ∨ p257 ∨ (¬ p1184)) : (¬ p69) ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p257) := by
    exact h16170
  have u6 : p1184 := by
    exact h7053
  rcases h12425 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step17526 (p2 p7 p40 p234 p1035 p1140 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h8348 : p1386)
    (h12426 : (¬ p2) ∨ p7 ∨ p40 ∨ (¬ p234) ∨ (¬ p1035) ∨ (¬ p1140) ∨ (¬ p1386)) : (¬ p2) ∨ (¬ p234) ∨ (¬ p1035) ∨ (¬ p1140) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p234 := by
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
  have u5 : (¬ p40) := by
    exact h16150
  have u6 : p1386 := by
    exact h8348
  rcases h12426 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17527 (p7 p85 p362 p434 p496 p1249 p1330 p1489 : Prop)
    (h16152 : (¬ p7))
    (h12427 : p7 ∨ (¬ p85) ∨ (¬ p362) ∨ (¬ p434) ∨ (¬ p496) ∨ (¬ p1249) ∨ (¬ p1330) ∨ (¬ p1489)) : (¬ p85) ∨ (¬ p362) ∨ (¬ p434) ∨ (¬ p496) ∨ (¬ p1249) ∨ (¬ p1330) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12427 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17528 (p2 p7 p102 p127 p325 p342 : Prop)
    (h16152 : (¬ p7))
    (h12428 : (¬ p2) ∨ p7 ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p325) ∨ (¬ p342)) : (¬ p2) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p325) ∨ (¬ p342) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p342 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12428 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17529 (p7 p419 p542 p666 p897 p1095 : Prop)
    (h16152 : (¬ p7))
    (h12429 : p7 ∨ (¬ p419) ∨ (¬ p542) ∨ (¬ p666) ∨ (¬ p897) ∨ (¬ p1095)) : (¬ p419) ∨ (¬ p542) ∨ (¬ p666) ∨ (¬ p897) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12429 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17530 (p7 p426 p897 p983 p1095 p1135 p1325 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h6744 : p1135)
    (h12431 : p7 ∨ p426 ∨ (¬ p897) ∨ (¬ p983) ∨ (¬ p1095) ∨ (¬ p1135) ∨ (¬ p1325)) : (¬ p897) ∨ (¬ p983) ∨ (¬ p1095) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1095 := by
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
  rcases h12431 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step17531 (p7 p70 p102 p127 p290 p840 p897 p1099 : Prop)
    (h16152 : (¬ p7))
    (h12432 : p7 ∨ (¬ p70) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p290) ∨ (¬ p840) ∨ (¬ p897) ∨ (¬ p1099)) : (¬ p70) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p290) ∨ (¬ p840) ∨ (¬ p897) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p290 := by
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
  rcases h12432 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17533 (p7 p185 p279 p426 p897 p1095 p1115 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16178 : (¬ p426))
    (h12434 : p7 ∨ (¬ p185) ∨ (¬ p279) ∨ p426 ∨ (¬ p897) ∨ (¬ p1095) ∨ (¬ p1115)) : (¬ p185) ∨ (¬ p897) ∨ (¬ p1095) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p279 := by
    exact h1444
  have u6 : (¬ p426) := by
    exact h16178
  rcases h12434 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17534 (p7 p87 p238 p928 p1055 p1116 : Prop)
    (h16152 : (¬ p7))
    (h12435 : p7 ∨ (¬ p87) ∨ (¬ p238) ∨ (¬ p928) ∨ (¬ p1055) ∨ (¬ p1116)) : (¬ p87) ∨ (¬ p238) ∨ (¬ p928) ∨ (¬ p1055) ∨ (¬ p1116) := by
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
  have u2 : p928 := by
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
  rcases h12435 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17535 (p7 p41 p189 p230 p242 p1061 p1115 p1537 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h9400 : p1537)
    (h12437 : p7 ∨ (¬ p41) ∨ (¬ p189) ∨ p230 ∨ (¬ p242) ∨ (¬ p1061) ∨ (¬ p1115) ∨ (¬ p1537)) : (¬ p41) ∨ (¬ p189) ∨ (¬ p242) ∨ (¬ p1061) ∨ (¬ p1115) := by
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
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p1537 := by
    exact h9400
  rcases h12437 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step17538 (p7 p10 p213 p368 p438 p687 : Prop)
    (h16152 : (¬ p7))
    (h12440 : p7 ∨ (¬ p10) ∨ (¬ p213) ∨ (¬ p368) ∨ (¬ p438) ∨ (¬ p687)) : (¬ p10) ∨ (¬ p213) ∨ (¬ p368) ∨ (¬ p438) ∨ (¬ p687) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12440 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17539 (p7 p142 p193 p323 p387 p791 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16213 : (¬ p791))
    (h6744 : p1135)
    (h12442 : p7 ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p323) ∨ (¬ p387) ∨ p791 ∨ (¬ p1135)) : (¬ p142) ∨ (¬ p193) ∨ (¬ p323) ∨ (¬ p387) := by
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
  have u2 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p791) := by
    exact h16213
  have u6 : p1135 := by
    exact h6744
  rcases h12442 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step17540 (p7 p10 p68 p105 p211 p229 p362 : Prop)
    (h16152 : (¬ p7))
    (h12443 : p7 ∨ (¬ p10) ∨ (¬ p68) ∨ (¬ p105) ∨ (¬ p211) ∨ (¬ p229) ∨ (¬ p362)) : (¬ p10) ∨ (¬ p68) ∨ (¬ p105) ∨ (¬ p211) ∨ (¬ p229) ∨ (¬ p362) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12443 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17541 (p7 p86 p161 p193 p424 p1232 p1330 p1366 : Prop)
    (h16152 : (¬ p7))
    (h12444 : p7 ∨ (¬ p86) ∨ (¬ p161) ∨ (¬ p193) ∨ (¬ p424) ∨ (¬ p1232) ∨ (¬ p1330) ∨ (¬ p1366)) : (¬ p86) ∨ (¬ p161) ∨ (¬ p193) ∨ (¬ p424) ∨ (¬ p1232) ∨ (¬ p1330) ∨ (¬ p1366) := by
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
  have u2 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1232 := by
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
  rcases h12444 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17542 (p7 p301 p362 p658 p1386 p1443 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16199 : (¬ p658))
    (h8348 : p1386)
    (h12445 : p7 ∨ (¬ p301) ∨ (¬ p362) ∨ p658 ∨ (¬ p1386) ∨ (¬ p1443) ∨ (¬ p1452)) : (¬ p301) ∨ (¬ p362) ∨ (¬ p1443) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p362 := by
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
  have u5 : (¬ p658) := by
    exact h16199
  have u6 : p1386 := by
    exact h8348
  rcases h12445 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17543 (p7 p224 p346 p430 p1075 p1286 p1545 : Prop)
    (h16152 : (¬ p7))
    (h16180 : (¬ p430))
    (h6478 : p1075)
    (h12446 : p7 ∨ (¬ p224) ∨ (¬ p346) ∨ p430 ∨ (¬ p1075) ∨ (¬ p1286) ∨ (¬ p1545)) : (¬ p224) ∨ (¬ p346) ∨ (¬ p1286) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p430) := by
    exact h16180
  have u6 : p1075 := by
    exact h6478
  rcases h12446 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17544 (p7 p101 p237 p788 p791 p1076 p1116 : Prop)
    (h16152 : (¬ p7))
    (h5066 : p788)
    (h16213 : (¬ p791))
    (h12447 : p7 ∨ (¬ p101) ∨ (¬ p237) ∨ (¬ p788) ∨ p791 ∨ (¬ p1076) ∨ (¬ p1116)) : (¬ p101) ∨ (¬ p237) ∨ (¬ p1076) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p788 := by
    exact h5066
  have u6 : (¬ p791) := by
    exact h16213
  rcases h12447 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17545 (p7 p86 p237 p616 p983 p1116 p1335 p1545 : Prop)
    (h16152 : (¬ p7))
    (h12448 : p7 ∨ (¬ p86) ∨ (¬ p237) ∨ (¬ p616) ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1335) ∨ (¬ p1545)) : (¬ p86) ∨ (¬ p237) ∨ (¬ p616) ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1335) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12448 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17546 (p7 p108 p330 p343 p481 p557 p840 p998 p1061 p1115 p1159 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16309 : (¬ p1324))
    (h12449 : p7 ∨ (¬ p108) ∨ (¬ p330) ∨ (¬ p343) ∨ (¬ p481) ∨ (¬ p557) ∨ (¬ p840) ∨ (¬ p998) ∨ (¬ p1061) ∨ (¬ p1115) ∨ (¬ p1159) ∨ p1324 ∨ (¬ p1325)) : (¬ p108) ∨ (¬ p330) ∨ (¬ p481) ∨ (¬ p557) ∨ (¬ p840) ∨ (¬ p998) ∨ (¬ p1061) ∨ (¬ p1115) ∨ (¬ p1159) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p998 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1115 := by
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
  have u11 : p343 := by
    exact h1950
  have u12 : (¬ p1324) := by
    exact h16309
  rcases h12449 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u8)
  · exact False.elim (u12 q11)
  · exact False.elim (q12 u9)

theorem step17547 (p7 p86 p256 p616 p1335 p1443 p1452 p1545 : Prop)
    (h16152 : (¬ p7))
    (h12450 : p7 ∨ (¬ p86) ∨ (¬ p256) ∨ (¬ p616) ∨ (¬ p1335) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p1545)) : (¬ p86) ∨ (¬ p256) ∨ (¬ p616) ∨ (¬ p1335) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12450 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17548 (p6 p7 p19 p229 p233 p481 p653 : Prop)
    (h16152 : (¬ p7))
    (h2345 : p233)
    (h16194 : (¬ p653))
    (h12451 : (¬ p6) ∨ p7 ∨ (¬ p19) ∨ (¬ p229) ∨ (¬ p233) ∨ (¬ p481) ∨ p653) : (¬ p6) ∨ (¬ p19) ∨ (¬ p229) ∨ (¬ p481) := by
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
  have u2 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p233 := by
    exact h2345
  have u6 : (¬ p653) := by
    exact h16194
  rcases h12451 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step17549 (p7 p101 p213 p286 p310 p1061 p1115 : Prop)
    (h16152 : (¬ p7))
    (h12452 : p7 ∨ (¬ p101) ∨ (¬ p213) ∨ (¬ p286) ∨ (¬ p310) ∨ (¬ p1061) ∨ (¬ p1115)) : (¬ p101) ∨ (¬ p213) ∨ (¬ p286) ∨ (¬ p310) ∨ (¬ p1061) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12452 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17550 (p7 p86 p121 p142 p193 p228 p616 p1287 : Prop)
    (h16152 : (¬ p7))
    (h12453 : p7 ∨ (¬ p86) ∨ (¬ p121) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p228) ∨ (¬ p616) ∨ (¬ p1287)) : (¬ p86) ∨ (¬ p121) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p228) ∨ (¬ p616) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12453 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17551 (p7 p129 p189 p237 p1075 p1076 p1116 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h6478 : p1075)
    (h12454 : p7 ∨ p129 ∨ (¬ p189) ∨ (¬ p237) ∨ (¬ p1075) ∨ (¬ p1076) ∨ (¬ p1116)) : (¬ p189) ∨ (¬ p237) ∨ (¬ p1076) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p1075 := by
    exact h6478
  rcases h12454 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17552 (p7 p129 p142 p207 p362 p387 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h8348 : p1386)
    (h12457 : p7 ∨ p129 ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p142) ∨ (¬ p207) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p1333) := by
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
  have u2 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p1386 := by
    exact h8348
  rcases h12457 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step17553 (p7 p134 p163 p257 p557 p1061 p1075 p1076 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h6478 : p1075)
    (h12458 : p7 ∨ (¬ p134) ∨ (¬ p163) ∨ p257 ∨ (¬ p557) ∨ (¬ p1061) ∨ (¬ p1075) ∨ (¬ p1076)) : (¬ p134) ∨ (¬ p163) ∨ (¬ p557) ∨ (¬ p1061) ∨ (¬ p1076) := by
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
  have u2 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p257) := by
    exact h16170
  have u7 : p1075 := by
    exact h6478
  rcases h12458 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step17554 (p7 p85 p347 p438 p617 p687 p836 p918 : Prop)
    (h16152 : (¬ p7))
    (h12460 : p7 ∨ (¬ p85) ∨ (¬ p347) ∨ (¬ p438) ∨ (¬ p617) ∨ (¬ p687) ∨ (¬ p836) ∨ (¬ p918)) : (¬ p85) ∨ (¬ p347) ∨ (¬ p438) ∨ (¬ p617) ∨ (¬ p687) ∨ (¬ p836) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p687 := by
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
  rcases h12460 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17555 (p7 p8 p47 p87 p110 p158 p189 p229 p346 p928 : Prop)
    (h16152 : (¬ p7))
    (h12461 : p7 ∨ (¬ p8) ∨ (¬ p47) ∨ (¬ p87) ∨ (¬ p110) ∨ (¬ p158) ∨ (¬ p189) ∨ (¬ p229) ∨ (¬ p346) ∨ (¬ p928)) : (¬ p8) ∨ (¬ p47) ∨ (¬ p87) ∨ (¬ p110) ∨ (¬ p158) ∨ (¬ p189) ∨ (¬ p229) ∨ (¬ p346) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
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
  have u3 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h12461 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17556 (p7 p45 p85 p110 p167 p1061 p1076 p1100 : Prop)
    (h16152 : (¬ p7))
    (h12462 : p7 ∨ (¬ p45) ∨ (¬ p85) ∨ (¬ p110) ∨ (¬ p167) ∨ (¬ p1061) ∨ (¬ p1076) ∨ (¬ p1100)) : (¬ p45) ∨ (¬ p85) ∨ (¬ p110) ∨ (¬ p167) ∨ (¬ p1061) ∨ (¬ p1076) ∨ (¬ p1100) := by
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
  have u2 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1100 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12462 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17557 (p7 p41 p83 p110 p166 p189 p918 p1061 p1076 p1100 : Prop)
    (h16152 : (¬ p7))
    (h12463 : p7 ∨ (¬ p41) ∨ (¬ p83) ∨ (¬ p110) ∨ (¬ p166) ∨ (¬ p189) ∨ (¬ p918) ∨ (¬ p1061) ∨ (¬ p1076) ∨ (¬ p1100)) : (¬ p41) ∨ (¬ p83) ∨ (¬ p110) ∨ (¬ p166) ∨ (¬ p189) ∨ (¬ p918) ∨ (¬ p1061) ∨ (¬ p1076) ∨ (¬ p1100) := by
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
  have u2 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p166 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1100 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h12463 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17558 (p7 p158 p230 p343 p344 p928 p1061 p1076 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h1950 : p343)
    (h12464 : p7 ∨ (¬ p158) ∨ p230 ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p928) ∨ (¬ p1061) ∨ (¬ p1076)) : (¬ p158) ∨ (¬ p344) ∨ (¬ p928) ∨ (¬ p1061) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p343 := by
    exact h1950
  rcases h12464 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17559 (p7 p129 p163 p343 p344 p557 p1061 p1076 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h1950 : p343)
    (h12465 : p7 ∨ p129 ∨ (¬ p163) ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p557) ∨ (¬ p1061) ∨ (¬ p1076)) : (¬ p163) ∨ (¬ p344) ∨ (¬ p557) ∨ (¬ p1061) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p343 := by
    exact h1950
  rcases h12465 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17560 (p7 p129 p424 p657 p734 p1135 p1366 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h6744 : p1135)
    (h12466 : p7 ∨ p129 ∨ (¬ p424) ∨ (¬ p657) ∨ (¬ p734) ∨ (¬ p1135) ∨ (¬ p1366)) : (¬ p424) ∨ (¬ p657) ∨ (¬ p734) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p424 := by
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
  have u3 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p1135 := by
    exact h6744
  rcases h12466 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step17561 (p7 p129 p142 p207 p310 p983 p1061 p1135 p1325 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h6744 : p1135)
    (h12468 : p7 ∨ p129 ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p310) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1135) ∨ (¬ p1325)) : (¬ p142) ∨ (¬ p207) ∨ (¬ p310) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1325) := by
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
  have u2 : p310 := by
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
  have u7 : (¬ p129) := by
    exact h16154
  have u8 : p1135 := by
    exact h6744
  rcases h12468 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u5)

theorem step17562 (p2 p7 p142 p191 p207 p362 p387 p431 p435 : Prop)
    (h16152 : (¬ p7))
    (h12469 : (¬ p2) ∨ p7 ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p207) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p431) ∨ (¬ p435)) : (¬ p2) ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p207) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p431) ∨ (¬ p435) := by
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
  have u4 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12469 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17563 (p2 p7 p19 p67 p207 p362 p419 p434 p1334 : Prop)
    (h16152 : (¬ p7))
    (h12471 : (¬ p2) ∨ p7 ∨ (¬ p19) ∨ (¬ p67) ∨ (¬ p207) ∨ (¬ p362) ∨ (¬ p419) ∨ (¬ p434) ∨ (¬ p1334)) : (¬ p2) ∨ (¬ p19) ∨ (¬ p67) ∨ (¬ p207) ∨ (¬ p362) ∨ (¬ p419) ∨ (¬ p434) ∨ (¬ p1334) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12471 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17564 (p3 p6 p7 p107 p129 p142 p343 p344 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h1950 : p343)
    (h12472 : (¬ p3) ∨ (¬ p6) ∨ p7 ∨ (¬ p107) ∨ p129 ∨ (¬ p142) ∨ (¬ p343) ∨ (¬ p344)) : (¬ p3) ∨ (¬ p6) ∨ (¬ p107) ∨ (¬ p142) ∨ (¬ p344) := by
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
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p343 := by
    exact h1950
  rcases h12472 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step17565 (p3 p7 p12 p133 p343 p344 p1076 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h1950 : p343)
    (h12474 : (¬ p3) ∨ p7 ∨ (¬ p12) ∨ p133 ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p1076)) : (¬ p3) ∨ (¬ p12) ∨ (¬ p344) ∨ (¬ p1076) := by
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
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p133) := by
    exact h16157
  have u6 : p343 := by
    exact h1950
  rcases h12474 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17566 (p7 p70 p102 p127 p343 p344 p616 p1287 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16309 : (¬ p1324))
    (h12478 : p7 ∨ (¬ p70) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p616) ∨ (¬ p1287) ∨ p1324 ∨ (¬ p1325)) : (¬ p70) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p344) ∨ (¬ p616) ∨ (¬ p1287) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1287 := by
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
  rcases h12478 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17567 (p7 p233 p435 p790 p1022 p1349 p1444 : Prop)
    (h16152 : (¬ p7))
    (h2345 : p233)
    (h16406 : (¬ p1444))
    (h12479 : p7 ∨ (¬ p233) ∨ (¬ p435) ∨ (¬ p790) ∨ (¬ p1022) ∨ (¬ p1349) ∨ p1444) : (¬ p435) ∨ (¬ p790) ∨ (¬ p1022) ∨ (¬ p1349) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p233 := by
    exact h2345
  have u6 : (¬ p1444) := by
    exact h16406
  rcases h12479 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step17568 (p7 p45 p129 p233 p435 p687 p816 p1393 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h2345 : p233)
    (h12480 : p7 ∨ (¬ p45) ∨ p129 ∨ (¬ p233) ∨ (¬ p435) ∨ (¬ p687) ∨ (¬ p816) ∨ (¬ p1393)) : (¬ p45) ∨ (¬ p435) ∨ (¬ p687) ∨ (¬ p816) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p687 := by
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
  have u7 : p233 := by
    exact h2345
  rcases h12480 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17569 (p7 p45 p802 p1015 p1392 p1542 : Prop)
    (h16152 : (¬ p7))
    (h12481 : p7 ∨ (¬ p45) ∨ (¬ p802) ∨ (¬ p1015) ∨ (¬ p1392) ∨ (¬ p1542)) : (¬ p45) ∨ (¬ p802) ∨ (¬ p1015) ∨ (¬ p1392) ∨ (¬ p1542) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p802 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1392 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12481 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17571 (p7 p70 p121 p127 p616 p1335 p1452 p1545 : Prop)
    (h16152 : (¬ p7))
    (h12483 : p7 ∨ (¬ p70) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p616) ∨ (¬ p1335) ∨ (¬ p1452) ∨ (¬ p1545)) : (¬ p70) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p616) ∨ (¬ p1335) ∨ (¬ p1452) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p70 := by
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
  have u3 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12483 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17572 (p6 p7 p109 p561 p1036 p1061 : Prop)
    (h16152 : (¬ p7))
    (h12484 : (¬ p6) ∨ p7 ∨ (¬ p109) ∨ (¬ p561) ∨ (¬ p1036) ∨ (¬ p1061)) : (¬ p6) ∨ (¬ p109) ∨ (¬ p561) ∨ (¬ p1036) ∨ (¬ p1061) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12484 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17573 (p7 p70 p85 p127 p323 p347 p836 p918 : Prop)
    (h16152 : (¬ p7))
    (h12485 : p7 ∨ (¬ p70) ∨ (¬ p85) ∨ (¬ p127) ∨ (¬ p323) ∨ (¬ p347) ∨ (¬ p836) ∨ (¬ p918)) : (¬ p70) ∨ (¬ p85) ∨ (¬ p127) ∨ (¬ p323) ∨ (¬ p347) ∨ (¬ p836) ∨ (¬ p918) := by
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
  have u2 : p127 := by
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
  rcases h12485 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17574 (p7 p290 p346 p833 p918 p1393 : Prop)
    (h16152 : (¬ p7))
    (h12486 : p7 ∨ (¬ p290) ∨ (¬ p346) ∨ (¬ p833) ∨ (¬ p918) ∨ (¬ p1393)) : (¬ p290) ∨ (¬ p346) ∨ (¬ p833) ∨ (¬ p918) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p290 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p833 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12486 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17575 (p7 p41 p121 p127 p187 p230 p1386 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h8348 : p1386)
    (h12488 : p7 ∨ (¬ p41) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p187) ∨ p230 ∨ (¬ p1386) ∨ (¬ p1452)) : (¬ p41) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p187) ∨ (¬ p1452) := by
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
  have u4 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p1386 := by
    exact h8348
  rcases h12488 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step17576 (p7 p41 p87 p161 p187 p481 p1272 p1330 p1349 p1366 : Prop)
    (h16152 : (¬ p7))
    (h12490 : p7 ∨ (¬ p41) ∨ (¬ p87) ∨ (¬ p161) ∨ (¬ p187) ∨ (¬ p481) ∨ (¬ p1272) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p1366)) : (¬ p41) ∨ (¬ p87) ∨ (¬ p161) ∨ (¬ p187) ∨ (¬ p481) ∨ (¬ p1272) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p1366) := by
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
  have u2 : p161 := by
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
  have u5 : p1272 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h12490 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17577 (p7 p17 p230 p581 p685 p790 p1022 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h3898 : p685)
    (h12492 : p7 ∨ (¬ p17) ∨ p230 ∨ (¬ p581) ∨ (¬ p685) ∨ (¬ p790) ∨ (¬ p1022)) : (¬ p17) ∨ (¬ p581) ∨ (¬ p790) ∨ (¬ p1022) := by
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
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p685 := by
    exact h3898
  rcases h12492 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17579 (p7 p70 p127 p161 p323 p434 p1232 p1330 : Prop)
    (h16152 : (¬ p7))
    (h12494 : p7 ∨ (¬ p70) ∨ (¬ p127) ∨ (¬ p161) ∨ (¬ p323) ∨ (¬ p434) ∨ (¬ p1232) ∨ (¬ p1330)) : (¬ p70) ∨ (¬ p127) ∨ (¬ p161) ∨ (¬ p323) ∨ (¬ p434) ∨ (¬ p1232) ∨ (¬ p1330) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12494 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17581 (p7 p127 p133 p323 p387 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h8348 : p1386)
    (h12496 : p7 ∨ (¬ p127) ∨ p133 ∨ (¬ p323) ∨ (¬ p387) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p127) ∨ (¬ p323) ∨ (¬ p387) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p133) := by
    exact h16157
  have u6 : p1386 := by
    exact h8348
  rcases h12496 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17582 (p7 p172 p225 p833 p918 p1393 : Prop)
    (h16152 : (¬ p7))
    (h12497 : p7 ∨ (¬ p172) ∨ (¬ p225) ∨ (¬ p833) ∨ (¬ p918) ∨ (¬ p1393)) : (¬ p172) ∨ (¬ p225) ∨ (¬ p833) ∨ (¬ p918) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p833 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12497 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17583 (p7 p172 p225 p382 p713 p789 p839 : Prop)
    (h16152 : (¬ p7))
    (h12498 : p7 ∨ (¬ p172) ∨ (¬ p225) ∨ (¬ p382) ∨ (¬ p713) ∨ (¬ p789) ∨ (¬ p839)) : (¬ p172) ∨ (¬ p225) ∨ (¬ p382) ∨ (¬ p713) ∨ (¬ p789) ∨ (¬ p839) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p713 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p839 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12498 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17584 (p7 p70 p85 p127 p323 p387 p431 p1387 p1545 : Prop)
    (h16152 : (¬ p7))
    (h12499 : p7 ∨ (¬ p70) ∨ (¬ p85) ∨ (¬ p127) ∨ (¬ p323) ∨ (¬ p387) ∨ (¬ p431) ∨ (¬ p1387) ∨ (¬ p1545)) : (¬ p70) ∨ (¬ p85) ∨ (¬ p127) ∨ (¬ p323) ∨ (¬ p387) ∨ (¬ p431) ∨ (¬ p1387) ∨ (¬ p1545) := by
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
  have u2 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12499 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17585 (p7 p70 p121 p127 p161 p228 p1232 p1333 : Prop)
    (h16152 : (¬ p7))
    (h12500 : p7 ∨ (¬ p70) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p161) ∨ (¬ p228) ∨ (¬ p1232) ∨ (¬ p1333)) : (¬ p70) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p161) ∨ (¬ p228) ∨ (¬ p1232) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p70 := by
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
  have u3 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12500 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17586 (p7 p290 p346 p382 p713 p789 p839 : Prop)
    (h16152 : (¬ p7))
    (h12501 : p7 ∨ (¬ p290) ∨ (¬ p346) ∨ (¬ p382) ∨ (¬ p713) ∨ (¬ p789) ∨ (¬ p839)) : (¬ p290) ∨ (¬ p346) ∨ (¬ p382) ∨ (¬ p713) ∨ (¬ p789) ∨ (¬ p839) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p290 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p713 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p839 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12501 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17587 (p7 p17 p42 p193 p258 p1076 p1181 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16272 : (¬ p1181))
    (h12502 : p7 ∨ (¬ p17) ∨ (¬ p42) ∨ (¬ p193) ∨ (¬ p258) ∨ (¬ p1076) ∨ p1181) : (¬ p17) ∨ (¬ p193) ∨ (¬ p258) ∨ (¬ p1076) := by
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
  have u2 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p42 := by
    exact h132
  have u6 : (¬ p1181) := by
    exact h16272
  rcases h12502 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step17588 (p7 p345 p438 p642 p728 p904 : Prop)
    (h16152 : (¬ p7))
    (h12505 : p7 ∨ (¬ p345) ∨ (¬ p438) ∨ (¬ p642) ∨ (¬ p728) ∨ (¬ p904)) : (¬ p345) ∨ (¬ p438) ∨ (¬ p642) ∨ (¬ p728) ∨ (¬ p904) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p642 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12505 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17589 (p7 p42 p193 p302 p419 p690 p815 p1366 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16285 : (¬ p302))
    (h12506 : p7 ∨ (¬ p42) ∨ (¬ p193) ∨ p302 ∨ (¬ p419) ∨ (¬ p690) ∨ (¬ p815) ∨ (¬ p1366)) : (¬ p193) ∨ (¬ p419) ∨ (¬ p690) ∨ (¬ p815) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p815 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p302) := by
    exact h16285
  rcases h12506 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (u7 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17590 (p7 p138 p193 p227 p262 p435 p798 p814 p1335 p1452 : Prop)
    (h16152 : (¬ p7))
    (h12507 : p7 ∨ (¬ p138) ∨ (¬ p193) ∨ (¬ p227) ∨ (¬ p262) ∨ (¬ p435) ∨ (¬ p798) ∨ (¬ p814) ∨ (¬ p1335) ∨ (¬ p1452)) : (¬ p138) ∨ (¬ p193) ∨ (¬ p227) ∨ (¬ p262) ∨ (¬ p435) ∨ (¬ p798) ∨ (¬ p814) ∨ (¬ p1335) ∨ (¬ p1452) := by
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
  have u2 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p798 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h12507 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17591 (p7 p42 p193 p419 p798 p814 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16309 : (¬ p1324))
    (h12508 : p7 ∨ (¬ p42) ∨ (¬ p193) ∨ (¬ p419) ∨ (¬ p798) ∨ (¬ p814) ∨ p1324 ∨ (¬ p1325)) : (¬ p193) ∨ (¬ p419) ∨ (¬ p798) ∨ (¬ p814) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p798 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p42 := by
    exact h132
  have u7 : (¬ p1324) := by
    exact h16309
  rcases h12508 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step17593 (p7 p17 p42 p162 p193 p581 p918 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16160 : (¬ p162))
    (h12510 : p7 ∨ (¬ p17) ∨ (¬ p42) ∨ p162 ∨ (¬ p193) ∨ (¬ p581) ∨ (¬ p918)) : (¬ p17) ∨ (¬ p193) ∨ (¬ p581) ∨ (¬ p918) := by
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
  have u2 : p581 := by
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
  have u6 : (¬ p162) := by
    exact h16160
  rcases h12510 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17594 (p7 p69 p344 p545 p1061 p1076 p1100 p1187 : Prop)
    (h16152 : (¬ p7))
    (h12511 : p7 ∨ (¬ p69) ∨ (¬ p344) ∨ (¬ p545) ∨ (¬ p1061) ∨ (¬ p1076) ∨ (¬ p1100) ∨ (¬ p1187)) : (¬ p69) ∨ (¬ p344) ∨ (¬ p545) ∨ (¬ p1061) ∨ (¬ p1076) ∨ (¬ p1100) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1100 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12511 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17595 (p7 p69 p362 p387 p496 p1333 p1473 p1710 : Prop)
    (h16152 : (¬ p7))
    (h12512 : p7 ∨ (¬ p69) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p496) ∨ (¬ p1333) ∨ (¬ p1473) ∨ (¬ p1710)) : (¬ p69) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p496) ∨ (¬ p1333) ∨ (¬ p1473) ∨ (¬ p1710) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1333 := by
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
  rcases h12512 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17596 (p7 p48 p138 p576 p1711 p1712 : Prop)
    (h16152 : (¬ p7))
    (h12513 : p7 ∨ (¬ p48) ∨ (¬ p138) ∨ (¬ p576) ∨ (¬ p1711) ∨ (¬ p1712)) : (¬ p48) ∨ (¬ p138) ∨ (¬ p576) ∨ (¬ p1711) ∨ (¬ p1712) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1711 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1712 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12513 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17597 (p7 p42 p193 p814 p875 p1015 p1366 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16220 : (¬ p875))
    (h12517 : p7 ∨ (¬ p42) ∨ (¬ p193) ∨ (¬ p814) ∨ p875 ∨ (¬ p1015) ∨ (¬ p1366)) : (¬ p193) ∨ (¬ p814) ∨ (¬ p1015) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p42 := by
    exact h132
  have u6 : (¬ p875) := by
    exact h16220
  rcases h12517 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17598 (p7 p45 p89 p193 p924 p1099 : Prop)
    (h16152 : (¬ p7))
    (h12518 : p7 ∨ (¬ p45) ∨ (¬ p89) ∨ (¬ p193) ∨ (¬ p924) ∨ (¬ p1099)) : (¬ p45) ∨ (¬ p89) ∨ (¬ p193) ∨ (¬ p924) ∨ (¬ p1099) := by
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
  have u3 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12518 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17599 (p7 p44 p63 p69 p802 p1393 : Prop)
    (h16152 : (¬ p7))
    (h12519 : p7 ∨ (¬ p44) ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p802) ∨ (¬ p1393)) : (¬ p44) ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p802) ∨ (¬ p1393) := by
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
  have u3 : p802 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12519 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17600 (p7 p63 p69 p110 p229 p310 p421 p577 p1061 p1076 : Prop)
    (h16152 : (¬ p7))
    (h12520 : p7 ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p110) ∨ (¬ p229) ∨ (¬ p310) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p1061) ∨ (¬ p1076)) : (¬ p63) ∨ (¬ p69) ∨ (¬ p110) ∨ (¬ p229) ∨ (¬ p310) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p1061) ∨ (¬ p1076) := by
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
  have u2 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p229 := by
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
  have u6 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h12520 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17601 (p7 p63 p382 p614 p1286 p1389 : Prop)
    (h16152 : (¬ p7))
    (h12521 : p7 ∨ (¬ p63) ∨ (¬ p382) ∨ (¬ p614) ∨ (¬ p1286) ∨ (¬ p1389)) : (¬ p63) ∨ (¬ p382) ∨ (¬ p614) ∨ (¬ p1286) ∨ (¬ p1389) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p614 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12521 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17602 (p7 p63 p344 p577 p616 p640 p906 p1076 p1095 : Prop)
    (h16152 : (¬ p7))
    (h12522 : p7 ∨ (¬ p63) ∨ (¬ p344) ∨ (¬ p577) ∨ (¬ p616) ∨ (¬ p640) ∨ (¬ p906) ∨ (¬ p1076) ∨ (¬ p1095)) : (¬ p63) ∨ (¬ p344) ∨ (¬ p577) ∨ (¬ p616) ∨ (¬ p640) ∨ (¬ p906) ∨ (¬ p1076) ∨ (¬ p1095) := by
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
  have u2 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p640 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p906 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12522 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17603 (p7 p19 p39 p63 p121 p228 p616 p1287 : Prop)
    (h16152 : (¬ p7))
    (h12523 : p7 ∨ (¬ p19) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p121) ∨ (¬ p228) ∨ (¬ p616) ∨ (¬ p1287)) : (¬ p19) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p121) ∨ (¬ p228) ∨ (¬ p616) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
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
  have u3 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12523 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17604 (p7 p39 p63 p68 p127 p323 p387 p1232 p1295 : Prop)
    (h16152 : (¬ p7))
    (h12524 : p7 ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p127) ∨ (¬ p323) ∨ (¬ p387) ∨ (¬ p1232) ∨ (¬ p1295)) : (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p127) ∨ (¬ p323) ∨ (¬ p387) ∨ (¬ p1232) ∨ (¬ p1295) := by
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
  have u3 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p387 := by
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
  rcases h12524 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17605 (p7 p63 p161 p310 p343 p344 p421 p577 p1061 p1076 p1232 p1324 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16309 : (¬ p1324))
    (h12525 : p7 ∨ (¬ p63) ∨ (¬ p161) ∨ (¬ p310) ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p1061) ∨ (¬ p1076) ∨ (¬ p1232) ∨ p1324) : (¬ p63) ∨ (¬ p161) ∨ (¬ p310) ∨ (¬ p344) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p1061) ∨ (¬ p1076) ∨ (¬ p1232) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p343 := by
    exact h1950
  have u11 : (¬ p1324) := by
    exact h16309
  rcases h12525 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u8)
  · exact False.elim (u11 q11)

theorem step17606 (p7 p39 p63 p68 p102 p127 p344 p616 p842 p1388 : Prop)
    (h16152 : (¬ p7))
    (h12526 : p7 ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p344) ∨ (¬ p616) ∨ (¬ p842) ∨ (¬ p1388)) : (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p344) ∨ (¬ p616) ∨ (¬ p842) ∨ (¬ p1388) := by
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
  have u3 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p842 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1388 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h12526 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17607 (p7 p12 p129 p163 p343 p344 p1076 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h1950 : p343)
    (h12527 : p7 ∨ (¬ p12) ∨ p129 ∨ (¬ p163) ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p1076)) : (¬ p12) ∨ (¬ p163) ∨ (¬ p344) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p343 := by
    exact h1950
  rcases h12527 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17608 (p7 p39 p68 p88 p121 p127 p814 p1015 p1335 p1452 : Prop)
    (h16152 : (¬ p7))
    (h12528 : p7 ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p814) ∨ (¬ p1015) ∨ (¬ p1335) ∨ (¬ p1452)) : (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p814) ∨ (¬ p1015) ∨ (¬ p1335) ∨ (¬ p1452) := by
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
  have u3 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h12528 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17609 (p7 p88 p310 p344 p421 p577 p690 p815 p842 p1022 p1061 p1076 : Prop)
    (h16152 : (¬ p7))
    (h12529 : p7 ∨ (¬ p88) ∨ (¬ p310) ∨ (¬ p344) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p690) ∨ (¬ p815) ∨ (¬ p842) ∨ (¬ p1022) ∨ (¬ p1061) ∨ (¬ p1076)) : (¬ p88) ∨ (¬ p310) ∨ (¬ p344) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p690) ∨ (¬ p815) ∨ (¬ p842) ∨ (¬ p1022) ∨ (¬ p1061) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
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
  have u3 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p815 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p842 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : (¬ p7) := by
    exact h16152
  rcases h12529 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
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

theorem step17610 (p7 p45 p70 p83 p102 p127 p129 p343 p344 p814 p1393 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h1950 : p343)
    (h12530 : p7 ∨ (¬ p45) ∨ (¬ p70) ∨ (¬ p83) ∨ (¬ p102) ∨ (¬ p127) ∨ p129 ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p814) ∨ (¬ p1393)) : (¬ p45) ∨ (¬ p70) ∨ (¬ p83) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p344) ∨ (¬ p814) ∨ (¬ p1393) := by
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
  have u2 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p814 := by
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
  have u10 : p343 := by
    exact h1950
  rcases h12530 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step17611 (p7 p102 p133 p211 p227 p343 p344 p1206 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h1950 : p343)
    (h12531 : p7 ∨ (¬ p102) ∨ p133 ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p1206)) : (¬ p102) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p344) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
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
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p133) := by
    exact h16157
  have u7 : p343 := by
    exact h1950
  rcases h12531 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17613 (p7 p595 p1232 p1289 p1334 p1542 : Prop)
    (h16152 : (¬ p7))
    (h12533 : p7 ∨ (¬ p595) ∨ (¬ p1232) ∨ (¬ p1289) ∨ (¬ p1334) ∨ (¬ p1542)) : (¬ p595) ∨ (¬ p1232) ∨ (¬ p1289) ∨ (¬ p1334) ∨ (¬ p1542) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1289 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12533 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17614 (p7 p11 p288 p312 p1061 p1079 : Prop)
    (h16152 : (¬ p7))
    (h12534 : p7 ∨ (¬ p11) ∨ (¬ p288) ∨ (¬ p312) ∨ (¬ p1061) ∨ (¬ p1079)) : (¬ p11) ∨ (¬ p288) ∨ (¬ p312) ∨ (¬ p1061) ∨ (¬ p1079) := by
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
  have u2 : p312 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1079 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12534 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17615 (p6 p7 p129 p142 p164 p561 p1036 p1061 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h789 : p164)
    (h12535 : (¬ p6) ∨ p7 ∨ p129 ∨ (¬ p142) ∨ (¬ p164) ∨ (¬ p561) ∨ (¬ p1036) ∨ (¬ p1061)) : (¬ p6) ∨ (¬ p142) ∨ (¬ p561) ∨ (¬ p1036) ∨ (¬ p1061) := by
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
  have u2 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p164 := by
    exact h789
  rcases h12535 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17616 (p7 p102 p312 p1061 p1079 p1206 : Prop)
    (h16152 : (¬ p7))
    (h12536 : p7 ∨ (¬ p102) ∨ (¬ p312) ∨ (¬ p1061) ∨ (¬ p1079) ∨ (¬ p1206)) : (¬ p102) ∨ (¬ p312) ∨ (¬ p1061) ∨ (¬ p1079) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p312 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1079 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12536 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17617 (p7 p290 p710 p840 p1061 p1076 : Prop)
    (h16152 : (¬ p7))
    (h12537 : p7 ∨ (¬ p290) ∨ (¬ p710) ∨ (¬ p840) ∨ (¬ p1061) ∨ (¬ p1076)) : (¬ p290) ∨ (¬ p710) ∨ (¬ p840) ∨ (¬ p1061) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p290 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12537 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17618 (p7 p14 p39 p63 p64 p226 : Prop)
    (h16152 : (¬ p7))
    (h12539 : p7 ∨ (¬ p14) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p64) ∨ (¬ p226)) : (¬ p14) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p64) ∨ (¬ p226) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
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
  have u4 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12539 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17619 (p3 p7 p12 p39 p63 p68 p642 p1076 p1099 : Prop)
    (h16152 : (¬ p7))
    (h12540 : (¬ p3) ∨ p7 ∨ (¬ p12) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p642) ∨ (¬ p1076) ∨ (¬ p1099)) : (¬ p3) ∨ (¬ p12) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p642) ∨ (¬ p1076) ∨ (¬ p1099) := by
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
  have u5 : p642 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12540 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17620 (p7 p10 p39 p63 p68 p102 p211 p362 p426 p897 p1075 p1099 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h6478 : p1075)
    (h12541 : p7 ∨ (¬ p10) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p102) ∨ (¬ p211) ∨ (¬ p362) ∨ p426 ∨ (¬ p897) ∨ (¬ p1075) ∨ (¬ p1099)) : (¬ p10) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p102) ∨ (¬ p211) ∨ (¬ p362) ∨ (¬ p897) ∨ (¬ p1099) := by
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
  have u4 : p102 := by
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
  have u7 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p426) := by
    exact h16178
  have u11 : p1075 := by
    exact h6478
  rcases h12541 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
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

theorem step17621 (p7 p39 p63 p68 p102 p211 p227 p642 p1099 p1206 : Prop)
    (h16152 : (¬ p7))
    (h12542 : p7 ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p102) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p642) ∨ (¬ p1099) ∨ (¬ p1206)) : (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p102) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p642) ∨ (¬ p1099) ∨ (¬ p1206) := by
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
  have u3 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p642 := by
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
  rcases h12542 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17623 (p7 p129 p142 p207 p368 p387 p438 p687 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h6744 : p1135)
    (h12544 : p7 ∨ p129 ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p368) ∨ (¬ p387) ∨ (¬ p438) ∨ (¬ p687) ∨ (¬ p1135)) : (¬ p142) ∨ (¬ p207) ∨ (¬ p368) ∨ (¬ p387) ∨ (¬ p438) ∨ (¬ p687) := by
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
  have u2 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p129) := by
    exact h16154
  have u8 : p1135 := by
    exact h6744
  rcases h12544 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u8)

theorem step17625 (p7 p85 p129 p142 p207 p362 p434 p858 p1184 p1334 p1385 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h7053 : p1184)
    (h12547 : p7 ∨ (¬ p85) ∨ p129 ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p362) ∨ (¬ p434) ∨ (¬ p858) ∨ (¬ p1184) ∨ (¬ p1334) ∨ (¬ p1385)) : (¬ p85) ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p362) ∨ (¬ p434) ∨ (¬ p858) ∨ (¬ p1334) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
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
  have u3 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p129) := by
    exact h16154
  have u10 : p1184 := by
    exact h7053
  rcases h12547 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step17626 (p6 p7 p19 p40 p561 p1061 p1075 p1076 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h6478 : p1075)
    (h12549 : (¬ p6) ∨ p7 ∨ (¬ p19) ∨ p40 ∨ (¬ p561) ∨ (¬ p1061) ∨ (¬ p1075) ∨ (¬ p1076)) : (¬ p6) ∨ (¬ p19) ∨ (¬ p561) ∨ (¬ p1061) ∨ (¬ p1076) := by
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
  have u2 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p40) := by
    exact h16150
  have u7 : p1075 := by
    exact h6478
  rcases h12549 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step17627 (p7 p70 p85 p121 p127 p228 p858 p1385 : Prop)
    (h16152 : (¬ p7))
    (h12550 : p7 ∨ (¬ p70) ∨ (¬ p85) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p228) ∨ (¬ p858) ∨ (¬ p1385)) : (¬ p70) ∨ (¬ p85) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p228) ∨ (¬ p858) ∨ (¬ p1385) := by
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
  have u4 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12550 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17628 (p7 p85 p224 p290 p346 p368 p406 p496 p918 : Prop)
    (h16152 : (¬ p7))
    (h12551 : p7 ∨ (¬ p85) ∨ (¬ p224) ∨ (¬ p290) ∨ (¬ p346) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p496) ∨ (¬ p918)) : (¬ p85) ∨ (¬ p224) ∨ (¬ p290) ∨ (¬ p346) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p496) ∨ (¬ p918) := by
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
  have u2 : p290 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12551 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17629 (p7 p312 p532 p983 p1061 p1078 : Prop)
    (h16152 : (¬ p7))
    (h12552 : p7 ∨ (¬ p312) ∨ (¬ p532) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1078)) : (¬ p312) ∨ (¬ p532) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1078) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p312 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p532 := by
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
  have u4 : p1078 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12552 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17630 (p7 p419 p542 p666 p710 p1061 : Prop)
    (h16152 : (¬ p7))
    (h12553 : p7 ∨ (¬ p419) ∨ (¬ p542) ∨ (¬ p666) ∨ (¬ p710) ∨ (¬ p1061)) : (¬ p419) ∨ (¬ p542) ∨ (¬ p666) ∨ (¬ p710) ∨ (¬ p1061) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12553 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17631 (p18 p27 p128 p1160 : Prop)
    (h653 : p128)
    (h16265 : (¬ p1160))
    (h12555 : (¬ p18) ∨ p27 ∨ (¬ p128) ∨ p1160) : (¬ p18) ∨ p27 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p27) := fun hu => hn (Or.inr hu)
  have u2 : p128 := by
    exact h653
  have u3 : (¬ p1160) := by
    exact h16265
  rcases h12555 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)

theorem step17632 (p7 p27 p324 p387 p419 p601 : Prop)
    (h16152 : (¬ p7))
    (h12557 : p7 ∨ (¬ p27) ∨ (¬ p324) ∨ (¬ p387) ∨ (¬ p419) ∨ (¬ p601)) : (¬ p27) ∨ (¬ p324) ∨ (¬ p387) ∨ (¬ p419) ∨ (¬ p601) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p27 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p324 := by
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
  have u4 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12557 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17633 (p7 p84 p163 p193 p499 p544 p582 p616 p906 : Prop)
    (h16152 : (¬ p7))
    (h12558 : p7 ∨ (¬ p84) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p499) ∨ (¬ p544) ∨ (¬ p582) ∨ (¬ p616) ∨ (¬ p906)) : (¬ p84) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p499) ∨ (¬ p544) ∨ (¬ p582) ∨ (¬ p616) ∨ (¬ p906) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p84 := by
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
  have u3 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p544 := by
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
  have u7 : p906 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12558 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17634 (p3 p7 p26 p68 p167 p424 p499 p616 p1195 : Prop)
    (h16152 : (¬ p7))
    (h12559 : (¬ p3) ∨ p7 ∨ (¬ p26) ∨ (¬ p68) ∨ (¬ p167) ∨ (¬ p424) ∨ (¬ p499) ∨ (¬ p616) ∨ (¬ p1195)) : (¬ p3) ∨ (¬ p26) ∨ (¬ p68) ∨ (¬ p167) ∨ (¬ p424) ∨ (¬ p499) ∨ (¬ p616) ∨ (¬ p1195) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p26 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12559 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17636 (p7 p10 p213 p303 p368 p406 : Prop)
    (h16152 : (¬ p7))
    (h12561 : p7 ∨ (¬ p10) ∨ (¬ p213) ∨ (¬ p303) ∨ (¬ p368) ∨ (¬ p406)) : (¬ p10) ∨ (¬ p213) ∨ (¬ p303) ∨ (¬ p368) ∨ (¬ p406) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12561 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17637 (p7 p323 p370 p384 p406 p1206 : Prop)
    (h16152 : (¬ p7))
    (h12562 : p7 ∨ (¬ p323) ∨ (¬ p370) ∨ (¬ p384) ∨ (¬ p406) ∨ (¬ p1206)) : (¬ p323) ∨ (¬ p370) ∨ (¬ p384) ∨ (¬ p406) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p370 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p384 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12562 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17638 (p7 p9 p495 p641 p1061 p1074 : Prop)
    (h16152 : (¬ p7))
    (h12564 : p7 ∨ (¬ p9) ∨ (¬ p495) ∨ (¬ p641) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p9) ∨ (¬ p495) ∨ (¬ p641) ∨ (¬ p1061) ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p641 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12564 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17639 (p7 p18 p68 p139 p301 p328 p481 : Prop)
    (h16152 : (¬ p7))
    (h12568 : p7 ∨ (¬ p18) ∨ (¬ p68) ∨ (¬ p139) ∨ (¬ p301) ∨ (¬ p328) ∨ (¬ p481)) : (¬ p18) ∨ (¬ p68) ∨ (¬ p139) ∨ (¬ p301) ∨ (¬ p328) ∨ (¬ p481) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p139 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p328 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12568 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17640 (p4 p7 p10 p163 p193 p544 p788 p791 : Prop)
    (h16152 : (¬ p7))
    (h5066 : p788)
    (h16213 : (¬ p791))
    (h12569 : (¬ p4) ∨ p7 ∨ (¬ p10) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p544) ∨ (¬ p788) ∨ p791) : (¬ p4) ∨ (¬ p10) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p544) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p10 := by
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
  have u4 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p788 := by
    exact h5066
  have u7 : (¬ p791) := by
    exact h16213
  rcases h12569 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u6)
  · exact False.elim (u7 q7)

theorem step17641 (p7 p108 p142 p193 p346 p544 p791 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16213 : (¬ p791))
    (h6478 : p1075)
    (h12571 : p7 ∨ (¬ p108) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p346) ∨ (¬ p544) ∨ p791 ∨ (¬ p1075)) : (¬ p108) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p346) ∨ (¬ p544) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p791) := by
    exact h16213
  have u7 : p1075 := by
    exact h6478
  rcases h12571 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u7)

theorem step17642 (p7 p86 p142 p193 p323 p427 p616 p1287 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h2334 : p427)
    (h16309 : (¬ p1324))
    (h12573 : p7 ∨ (¬ p86) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p323) ∨ (¬ p427) ∨ (¬ p616) ∨ (¬ p1287) ∨ p1324 ∨ (¬ p1325)) : (¬ p86) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p323) ∨ (¬ p616) ∨ (¬ p1287) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p427 := by
    exact h2334
  have u9 : (¬ p1324) := by
    exact h16309
  rcases h12573 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17643 (p7 p69 p362 p419 p434 p496 p1187 p1334 : Prop)
    (h16152 : (¬ p7))
    (h12574 : p7 ∨ (¬ p69) ∨ (¬ p362) ∨ (¬ p419) ∨ (¬ p434) ∨ (¬ p496) ∨ (¬ p1187) ∨ (¬ p1334)) : (¬ p69) ∨ (¬ p362) ∨ (¬ p419) ∨ (¬ p434) ∨ (¬ p496) ∨ (¬ p1187) ∨ (¬ p1334) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12574 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17645 (p7 p138 p160 p193 p228 p236 p262 p532 p814 p858 : Prop)
    (h16152 : (¬ p7))
    (h12576 : p7 ∨ (¬ p138) ∨ (¬ p160) ∨ (¬ p193) ∨ (¬ p228) ∨ (¬ p236) ∨ (¬ p262) ∨ (¬ p532) ∨ (¬ p814) ∨ (¬ p858)) : (¬ p138) ∨ (¬ p160) ∨ (¬ p193) ∨ (¬ p228) ∨ (¬ p236) ∨ (¬ p262) ∨ (¬ p532) ∨ (¬ p814) ∨ (¬ p858) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p236 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h12576 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17646 (p7 p138 p193 p262 p310 p864 p983 p1061 p1325 p1349 : Prop)
    (h16152 : (¬ p7))
    (h12578 : p7 ∨ (¬ p138) ∨ (¬ p193) ∨ (¬ p262) ∨ (¬ p310) ∨ (¬ p864) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1325) ∨ (¬ p1349)) : (¬ p138) ∨ (¬ p193) ∨ (¬ p262) ∨ (¬ p310) ∨ (¬ p864) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1325) ∨ (¬ p1349) := by
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
  have u3 : p310 := by
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
  have u7 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h12578 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17649 (p7 p138 p185 p193 p262 p362 p387 p426 p836 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h8348 : p1386)
    (h12581 : p7 ∨ (¬ p138) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p262) ∨ (¬ p362) ∨ (¬ p387) ∨ p426 ∨ (¬ p836) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p138) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p262) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p836) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p138 := by
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
  have u3 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p836 := by
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
  rcases h12581 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step17650 (p7 p42 p185 p193 p544 p653 p836 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16194 : (¬ p653))
    (h12582 : p7 ∨ (¬ p42) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p544) ∨ p653 ∨ (¬ p836)) : (¬ p185) ∨ (¬ p193) ∨ (¬ p544) ∨ (¬ p836) := by
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
  have u2 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p42 := by
    exact h132
  have u6 : (¬ p653) := by
    exact h16194
  rcases h12582 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step17651 (p7 p381 p521 p532 p789 p1333 : Prop)
    (h16152 : (¬ p7))
    (h12583 : p7 ∨ (¬ p381) ∨ (¬ p521) ∨ (¬ p532) ∨ (¬ p789) ∨ (¬ p1333)) : (¬ p381) ∨ (¬ p521) ∨ (¬ p532) ∨ (¬ p789) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p381 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p521 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12583 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17652 (p7 p41 p42 p162 p185 p256 p576 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16160 : (¬ p162))
    (h12586 : p7 ∨ (¬ p41) ∨ (¬ p42) ∨ p162 ∨ (¬ p185) ∨ (¬ p256) ∨ (¬ p576)) : (¬ p41) ∨ (¬ p185) ∨ (¬ p256) ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
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
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p42 := by
    exact h132
  have u6 : (¬ p162) := by
    exact h16160
  rcases h12586 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17653 (p7 p102 p127 p133 p983 p1077 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h8348 : p1386)
    (h12587 : p7 ∨ (¬ p102) ∨ (¬ p127) ∨ p133 ∨ (¬ p983) ∨ (¬ p1077) ∨ (¬ p1386)) : (¬ p102) ∨ (¬ p127) ∨ (¬ p983) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p133) := by
    exact h16157
  have u6 : p1386 := by
    exact h8348
  rcases h12587 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17654 (p7 p45 p135 p580 p1611 p1644 : Prop)
    (h16152 : (¬ p7))
    (h12588 : p7 ∨ (¬ p45) ∨ (¬ p135) ∨ (¬ p580) ∨ (¬ p1611) ∨ (¬ p1644)) : (¬ p45) ∨ (¬ p135) ∨ (¬ p580) ∨ (¬ p1611) ∨ (¬ p1644) := by
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
  have u2 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1611 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12588 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17655 (p7 p40 p69 p343 p595 p734 p1542 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h1950 : p343)
    (h12589 : p7 ∨ p40 ∨ (¬ p69) ∨ (¬ p343) ∨ (¬ p595) ∨ (¬ p734) ∨ (¬ p1542)) : (¬ p69) ∨ (¬ p595) ∨ (¬ p734) ∨ (¬ p1542) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p595 := by
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
  have u5 : (¬ p40) := by
    exact h16150
  have u6 : p343 := by
    exact h1950
  rcases h12589 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17656 (p7 p40 p69 p233 p419 p595 p1286 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h2345 : p233)
    (h12590 : p7 ∨ p40 ∨ (¬ p69) ∨ (¬ p233) ∨ (¬ p419) ∨ (¬ p595) ∨ (¬ p1286)) : (¬ p69) ∨ (¬ p419) ∨ (¬ p595) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p419 := by
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
  have u6 : p233 := by
    exact h2345
  rcases h12590 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17657 (p7 p39 p63 p68 p101 p124 p211 p323 p603 p616 : Prop)
    (h16152 : (¬ p7))
    (h12592 : p7 ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p211) ∨ (¬ p323) ∨ (¬ p603) ∨ (¬ p616)) : (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p211) ∨ (¬ p323) ∨ (¬ p603) ∨ (¬ p616) := by
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
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p603 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h12592 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17659 (p7 p39 p63 p68 p351 p544 p561 p597 p616 p1036 p1061 : Prop)
    (h16152 : (¬ p7))
    (h12594 : p7 ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p351) ∨ (¬ p544) ∨ (¬ p561) ∨ (¬ p597) ∨ (¬ p616) ∨ (¬ p1036) ∨ (¬ p1061)) : (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p351) ∨ (¬ p544) ∨ (¬ p561) ∨ (¬ p597) ∨ (¬ p616) ∨ (¬ p1036) ∨ (¬ p1061) := by
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
  have u3 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p597 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h12594 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step17660 (p7 p39 p69 p498 p575 p1604 p1631 : Prop)
    (h16152 : (¬ p7))
    (h12595 : p7 ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p498) ∨ (¬ p575) ∨ (¬ p1604) ∨ (¬ p1631)) : (¬ p39) ∨ (¬ p69) ∨ (¬ p498) ∨ (¬ p575) ∨ (¬ p1604) ∨ (¬ p1631) := by
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
  have u2 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p575 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1604 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1631 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12595 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17661 (p3 p7 p12 p190 p258 p261 p686 p983 p1386 p1624 p1651 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h8348 : p1386)
    (h12596 : (¬ p3) ∨ p7 ∨ (¬ p12) ∨ (¬ p190) ∨ (¬ p258) ∨ (¬ p261) ∨ p686 ∨ (¬ p983) ∨ (¬ p1386) ∨ (¬ p1624) ∨ (¬ p1651)) : (¬ p3) ∨ (¬ p12) ∨ (¬ p190) ∨ (¬ p258) ∨ (¬ p261) ∨ (¬ p983) ∨ (¬ p1624) ∨ (¬ p1651) := by
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
  have u2 : p190 := by
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
  have u5 : p983 := by
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
  rcases h12596 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u9 q6)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step17662 (p3 p7 p12 p17 p190 p983 p1454 p1644 : Prop)
    (h16152 : (¬ p7))
    (h12597 : (¬ p3) ∨ p7 ∨ (¬ p12) ∨ (¬ p17) ∨ (¬ p190) ∨ (¬ p983) ∨ (¬ p1454) ∨ (¬ p1644)) : (¬ p3) ∨ (¬ p12) ∨ (¬ p17) ∨ (¬ p190) ∨ (¬ p983) ∨ (¬ p1454) ∨ (¬ p1644) := by
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
  have u4 : p983 := by
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
  rcases h12597 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17664 (p7 p87 p125 p126 p261 p581 : Prop)
    (h16152 : (¬ p7))
    (h12602 : p7 ∨ (¬ p87) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p261) ∨ (¬ p581)) : (¬ p87) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p261) ∨ (¬ p581) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12602 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17665 (p7 p10 p143 p518 p576 p1393 : Prop)
    (h16152 : (¬ p7))
    (h12603 : p7 ∨ (¬ p10) ∨ (¬ p143) ∨ (¬ p518) ∨ (¬ p576) ∨ (¬ p1393)) : (¬ p10) ∨ (¬ p143) ∨ (¬ p518) ∨ (¬ p576) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p143 := by
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
  rcases h12603 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17666 (p7 p160 p189 p1257 p1353 p1489 : Prop)
    (h16152 : (¬ p7))
    (h12604 : p7 ∨ (¬ p160) ∨ (¬ p189) ∨ (¬ p1257) ∨ (¬ p1353) ∨ (¬ p1489)) : (¬ p160) ∨ (¬ p189) ∨ (¬ p1257) ∨ (¬ p1353) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1257 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1353 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12604 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17667 (p3 p7 p12 p135 p187 p256 p983 p1516 p1751 : Prop)
    (h16152 : (¬ p7))
    (h12605 : (¬ p3) ∨ p7 ∨ (¬ p12) ∨ (¬ p135) ∨ (¬ p187) ∨ (¬ p256) ∨ (¬ p983) ∨ (¬ p1516) ∨ (¬ p1751)) : (¬ p3) ∨ (¬ p12) ∨ (¬ p135) ∨ (¬ p187) ∨ (¬ p256) ∨ (¬ p983) ∨ (¬ p1516) ∨ (¬ p1751) := by
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
  have u2 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1516 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1751 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12605 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17668 (p7 p84 p435 p803 p1020 p1385 p1758 : Prop)
    (h16152 : (¬ p7))
    (h12606 : p7 ∨ (¬ p84) ∨ (¬ p435) ∨ (¬ p803) ∨ (¬ p1020) ∨ (¬ p1385) ∨ (¬ p1758)) : (¬ p84) ∨ (¬ p435) ∨ (¬ p803) ∨ (¬ p1020) ∨ (¬ p1385) ∨ (¬ p1758) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p803 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1020 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1758 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12606 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17669 (p7 p10 p126 p129 p189 p256 p788 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h5066 : p788)
    (h12608 : p7 ∨ (¬ p10) ∨ (¬ p126) ∨ p129 ∨ (¬ p189) ∨ (¬ p256) ∨ (¬ p788)) : (¬ p10) ∨ (¬ p126) ∨ (¬ p189) ∨ (¬ p256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p788 := by
    exact h5066
  rcases h12608 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17670 (p7 p135 p189 p266 p301 p362 : Prop)
    (h16152 : (¬ p7))
    (h12609 : p7 ∨ (¬ p135) ∨ (¬ p189) ∨ (¬ p266) ∨ (¬ p301) ∨ (¬ p362)) : (¬ p135) ∨ (¬ p189) ∨ (¬ p266) ∨ (¬ p301) ∨ (¬ p362) := by
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
  have u2 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12609 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17671 (p7 p70 p406 p419 p444 p475 p495 p1366 p1604 : Prop)
    (h16152 : (¬ p7))
    (h12610 : p7 ∨ (¬ p70) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p444) ∨ (¬ p475) ∨ (¬ p495) ∨ (¬ p1366) ∨ (¬ p1604)) : (¬ p70) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p444) ∨ (¬ p475) ∨ (¬ p495) ∨ (¬ p1366) ∨ (¬ p1604) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p444 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p475 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1604 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12610 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17672 (p7 p68 p104 p127 p229 p323 p350 : Prop)
    (h16152 : (¬ p7))
    (h12611 : p7 ∨ (¬ p68) ∨ (¬ p104) ∨ (¬ p127) ∨ (¬ p229) ∨ (¬ p323) ∨ (¬ p350)) : (¬ p68) ∨ (¬ p104) ∨ (¬ p127) ∨ (¬ p229) ∨ (¬ p323) ∨ (¬ p350) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p104 := by
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
  have u4 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12611 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17673 (p7 p327 p386 p419 p1325 p1452 : Prop)
    (h16152 : (¬ p7))
    (h12612 : p7 ∨ (¬ p327) ∨ (¬ p386) ∨ (¬ p419) ∨ (¬ p1325) ∨ (¬ p1452)) : (¬ p327) ∨ (¬ p386) ∨ (¬ p419) ∨ (¬ p1325) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p386 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
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
  rcases h12612 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17674 (p7 p85 p301 p430 p438 p576 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16180 : (¬ p430))
    (h7053 : p1184)
    (h12613 : p7 ∨ (¬ p85) ∨ (¬ p301) ∨ p430 ∨ (¬ p438) ∨ (¬ p576) ∨ (¬ p1184)) : (¬ p85) ∨ (¬ p301) ∨ (¬ p438) ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p430) := by
    exact h16180
  have u6 : p1184 := by
    exact h7053
  rcases h12613 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17675 (p3 p7 p70 p83 p544 p842 p1273 p1349 p1385 : Prop)
    (h16152 : (¬ p7))
    (h12614 : (¬ p3) ∨ p7 ∨ (¬ p70) ∨ (¬ p83) ∨ (¬ p544) ∨ (¬ p842) ∨ (¬ p1273) ∨ (¬ p1349) ∨ (¬ p1385)) : (¬ p3) ∨ (¬ p70) ∨ (¬ p83) ∨ (¬ p544) ∨ (¬ p842) ∨ (¬ p1273) ∨ (¬ p1349) ∨ (¬ p1385) := by
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
  have u2 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p842 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12614 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17676 (p7 p17 p83 p581 p1184 p1249 p1324 p1489 : Prop)
    (h16152 : (¬ p7))
    (h7053 : p1184)
    (h16309 : (¬ p1324))
    (h12615 : p7 ∨ (¬ p17) ∨ (¬ p83) ∨ (¬ p581) ∨ (¬ p1184) ∨ (¬ p1249) ∨ p1324 ∨ (¬ p1489)) : (¬ p17) ∨ (¬ p83) ∨ (¬ p581) ∨ (¬ p1249) ∨ (¬ p1489) := by
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
  rcases h12615 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step17678 (p7 p19 p280 p386 p788 p1141 p1452 p1465 : Prop)
    (h16152 : (¬ p7))
    (h16173 : (¬ p280))
    (h5066 : p788)
    (h12618 : p7 ∨ (¬ p19) ∨ p280 ∨ (¬ p386) ∨ (¬ p788) ∨ (¬ p1141) ∨ (¬ p1452) ∨ (¬ p1465)) : (¬ p19) ∨ (¬ p386) ∨ (¬ p1141) ∨ (¬ p1452) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p386 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p280) := by
    exact h16173
  have u7 : p788 := by
    exact h5066
  rcases h12618 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17679 (p7 p127 p161 p280 p386 p788 p1145 p1159 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16173 : (¬ p280))
    (h5066 : p788)
    (h12619 : p7 ∨ (¬ p127) ∨ (¬ p161) ∨ p280 ∨ (¬ p386) ∨ (¬ p788) ∨ (¬ p1145) ∨ (¬ p1159) ∨ (¬ p1452)) : (¬ p127) ∨ (¬ p161) ∨ (¬ p386) ∨ (¬ p1145) ∨ (¬ p1159) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p386 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1145 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p280) := by
    exact h16173
  have u8 : p788 := by
    exact h5066
  rcases h12619 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u7 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step17680 (p7 p63 p346 p426 p495 p636 p792 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h4535 : p792)
    (h12621 : p7 ∨ (¬ p63) ∨ (¬ p346) ∨ p426 ∨ (¬ p495) ∨ (¬ p636) ∨ (¬ p792)) : (¬ p63) ∨ (¬ p346) ∨ (¬ p495) ∨ (¬ p636) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p426) := by
    exact h16178
  have u6 : p792 := by
    exact h4535
  rcases h12621 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17681 (p7 p17 p45 p279 p581 p796 p875 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16220 : (¬ p875))
    (h12622 : p7 ∨ (¬ p17) ∨ (¬ p45) ∨ (¬ p279) ∨ (¬ p581) ∨ (¬ p796) ∨ p875) : (¬ p17) ∨ (¬ p45) ∨ (¬ p581) ∨ (¬ p796) := by
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
  have u3 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p279 := by
    exact h1444
  have u6 : (¬ p875) := by
    exact h16220
  rcases h12622 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step17685 (p7 p63 p304 p494 p577 p633 : Prop)
    (h16152 : (¬ p7))
    (h12626 : p7 ∨ (¬ p63) ∨ (¬ p304) ∨ (¬ p494) ∨ (¬ p577) ∨ (¬ p633)) : (¬ p63) ∨ (¬ p304) ∨ (¬ p494) ∨ (¬ p577) ∨ (¬ p633) := by
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
  have u2 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12626 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17686 (p7 p17 p123 p233 p419 p789 p790 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h2345 : p233)
    (h12627 : p7 ∨ (¬ p17) ∨ p123 ∨ (¬ p233) ∨ (¬ p419) ∨ (¬ p789) ∨ (¬ p790)) : (¬ p17) ∨ (¬ p419) ∨ (¬ p789) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p419 := by
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
  have u5 : (¬ p123) := by
    exact h16186
  have u6 : p233 := by
    exact h2345
  rcases h12627 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17687 (p3 p7 p70 p161 p544 p728 p1232 p1330 : Prop)
    (h16152 : (¬ p7))
    (h12628 : (¬ p3) ∨ p7 ∨ (¬ p70) ∨ (¬ p161) ∨ (¬ p544) ∨ (¬ p728) ∨ (¬ p1232) ∨ (¬ p1330)) : (¬ p3) ∨ (¬ p70) ∨ (¬ p161) ∨ (¬ p544) ∨ (¬ p728) ∨ (¬ p1232) ∨ (¬ p1330) := by
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
  have u2 : p161 := by
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
  have u5 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12628 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17688 (p7 p87 p185 p419 p542 p789 p897 p926 p1393 : Prop)
    (h16152 : (¬ p7))
    (h12630 : p7 ∨ (¬ p87) ∨ (¬ p185) ∨ (¬ p419) ∨ (¬ p542) ∨ (¬ p789) ∨ (¬ p897) ∨ (¬ p926) ∨ (¬ p1393)) : (¬ p87) ∨ (¬ p185) ∨ (¬ p419) ∨ (¬ p542) ∨ (¬ p789) ∨ (¬ p897) ∨ (¬ p926) ∨ (¬ p1393) := by
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
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12630 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17689 (p7 p63 p455 p494 p577 p961 : Prop)
    (h16152 : (¬ p7))
    (h12632 : p7 ∨ (¬ p63) ∨ (¬ p455) ∨ (¬ p494) ∨ (¬ p577) ∨ (¬ p961)) : (¬ p63) ∨ (¬ p455) ∨ (¬ p494) ∨ (¬ p577) ∨ (¬ p961) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12632 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17691 (p7 p10 p45 p129 p262 p362 p581 p788 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h5066 : p788)
    (h12638 : p7 ∨ (¬ p10) ∨ (¬ p45) ∨ p129 ∨ (¬ p262) ∨ (¬ p362) ∨ (¬ p581) ∨ (¬ p788)) : (¬ p10) ∨ (¬ p45) ∨ (¬ p262) ∨ (¬ p362) ∨ (¬ p581) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p788 := by
    exact h5066
  rcases h12638 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step17692 (p7 p233 p304 p362 p387 p419 p686 : Prop)
    (h16152 : (¬ p7))
    (h2345 : p233)
    (h16205 : (¬ p686))
    (h12639 : p7 ∨ (¬ p233) ∨ (¬ p304) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p419) ∨ p686) : (¬ p304) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p362 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p233 := by
    exact h2345
  have u6 : (¬ p686) := by
    exact h16205
  rcases h12639 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step17694 (p7 p193 p267 p304 p726 p985 p1035 p1256 : Prop)
    (h16152 : (¬ p7))
    (h12642 : p7 ∨ (¬ p193) ∨ (¬ p267) ∨ (¬ p304) ∨ (¬ p726) ∨ (¬ p985) ∨ (¬ p1035) ∨ (¬ p1256)) : (¬ p193) ∨ (¬ p267) ∨ (¬ p304) ∨ (¬ p726) ∨ (¬ p985) ∨ (¬ p1035) ∨ (¬ p1256) := by
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
  have u2 : p304 := by
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
  have u6 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12642 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17695 (p7 p406 p419 p475 p1369 p1798 : Prop)
    (h16152 : (¬ p7))
    (h12643 : p7 ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p475) ∨ (¬ p1369) ∨ (¬ p1798)) : (¬ p406) ∨ (¬ p419) ∨ (¬ p475) ∨ (¬ p1369) ∨ (¬ p1798) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p475 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1369 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1798 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12643 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17696 (p7 p135 p187 p406 p475 p581 p1287 p1387 : Prop)
    (h16152 : (¬ p7))
    (h12769 : p7 ∨ (¬ p135) ∨ (¬ p187) ∨ (¬ p406) ∨ (¬ p475) ∨ (¬ p581) ∨ (¬ p1287) ∨ (¬ p1387)) : (¬ p135) ∨ (¬ p187) ∨ (¬ p406) ∨ (¬ p475) ∨ (¬ p581) ∨ (¬ p1287) ∨ (¬ p1387) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p475 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p581 := by
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
  rcases h12769 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17697 (p7 p72 p406 p419 p475 p1187 : Prop)
    (h16152 : (¬ p7))
    (h12770 : p7 ∨ (¬ p72) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p475) ∨ (¬ p1187)) : (¬ p72) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p475) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p475 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12770 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17699 (p7 p12 p14 p15 p983 p1136 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16259 : (¬ p1136))
    (h8348 : p1386)
    (h12772 : p7 ∨ (¬ p12) ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p983) ∨ p1136 ∨ (¬ p1386)) : (¬ p12) ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p983) := by
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
  have u3 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p1136) := by
    exact h16259
  have u6 : p1386 := by
    exact h8348
  rcases h12772 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step17700 (p7 p15 p423 p980 p1035 p1136 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16259 : (¬ p1136))
    (h6761 : p1139)
    (h12773 : p7 ∨ (¬ p15) ∨ (¬ p423) ∨ (¬ p980) ∨ (¬ p1035) ∨ p1136 ∨ (¬ p1139)) : (¬ p15) ∨ (¬ p423) ∨ (¬ p980) ∨ (¬ p1035) := by
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
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p1136) := by
    exact h16259
  have u6 : p1139 := by
    exact h6761
  rcases h12773 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step17701 (p3 p7 p12 p72 p879 p1074 : Prop)
    (h16152 : (¬ p7))
    (h12775 : (¬ p3) ∨ p7 ∨ (¬ p12) ∨ (¬ p72) ∨ (¬ p879) ∨ (¬ p1074)) : (¬ p3) ∨ (¬ p12) ∨ (¬ p72) ∨ (¬ p879) ∨ (¬ p1074) := by
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
  have u2 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p879 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12775 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17702 (p7 p72 p211 p229 p310 p1036 p1061 : Prop)
    (h16152 : (¬ p7))
    (h12776 : p7 ∨ (¬ p72) ∨ (¬ p211) ∨ (¬ p229) ∨ (¬ p310) ∨ (¬ p1036) ∨ (¬ p1061)) : (¬ p72) ∨ (¬ p211) ∨ (¬ p229) ∨ (¬ p310) ∨ (¬ p1036) ∨ (¬ p1061) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12776 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17703 (p7 p63 p500 p532 p533 p537 p928 p961 : Prop)
    (h16152 : (¬ p7))
    (h12778 : p7 ∨ (¬ p63) ∨ (¬ p500) ∨ (¬ p532) ∨ (¬ p533) ∨ (¬ p537) ∨ (¬ p928) ∨ (¬ p961)) : (¬ p63) ∨ (¬ p500) ∨ (¬ p532) ∨ (¬ p533) ∨ (¬ p537) ∨ (¬ p928) ∨ (¬ p961) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p537 := by
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
  rcases h12778 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17704 (p3 p7 p71 p343 p534 p840 p1136 p1584 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16259 : (¬ p1136))
    (h12779 : (¬ p3) ∨ p7 ∨ (¬ p71) ∨ (¬ p343) ∨ (¬ p534) ∨ (¬ p840) ∨ p1136 ∨ (¬ p1584)) : (¬ p3) ∨ (¬ p71) ∨ (¬ p534) ∨ (¬ p840) ∨ (¬ p1584) := by
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
  have u2 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p343 := by
    exact h1950
  have u7 : (¬ p1136) := by
    exact h16259
  rcases h12779 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step17705 (p3 p7 p45 p90 p167 p186 : Prop)
    (h16152 : (¬ p7))
    (h12780 : (¬ p3) ∨ p7 ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p167) ∨ (¬ p186)) : (¬ p3) ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p167) ∨ (¬ p186) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
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
  have u3 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12780 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17707 (p7 p18 p42 p101 p422 p423 p686 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16205 : (¬ p686))
    (h12782 : p7 ∨ (¬ p18) ∨ (¬ p42) ∨ (¬ p101) ∨ (¬ p422) ∨ (¬ p423) ∨ p686) : (¬ p18) ∨ (¬ p101) ∨ (¬ p422) ∨ (¬ p423) := by
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
  have u2 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p42 := by
    exact h132
  have u6 : (¬ p686) := by
    exact h16205
  rcases h12782 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step17709 (p304 p642 p681 p919 : Prop)
    (h3892 : p681)
    (h16230 : (¬ p919))
    (h12784 : (¬ p304) ∨ p642 ∨ (¬ p681) ∨ p919) : (¬ p304) ∨ p642 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p642) := fun hu => hn (Or.inr hu)
  have u2 : p681 := by
    exact h3892
  have u3 : (¬ p919) := by
    exact h16230
  rcases h12784 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)

theorem step17710 (p7 p346 p435 p542 p736 p756 : Prop)
    (h16152 : (¬ p7))
    (h12785 : p7 ∨ (¬ p346) ∨ (¬ p435) ∨ (¬ p542) ∨ (¬ p736) ∨ (¬ p756)) : (¬ p346) ∨ (¬ p435) ∨ (¬ p542) ∨ (¬ p736) ∨ (¬ p756) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p736 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12785 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17711 (p3 p7 p16 p17 p71 p229 p234 p301 p327 : Prop)
    (h16152 : (¬ p7))
    (h12786 : (¬ p3) ∨ p7 ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p234) ∨ (¬ p301) ∨ (¬ p327)) : (¬ p3) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p234) ∨ (¬ p301) ∨ (¬ p327) := by
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
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12786 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17712 (p7 p14 p15 p16 p17 p301 p351 p544 : Prop)
    (h16152 : (¬ p7))
    (h12787 : p7 ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p301) ∨ (¬ p351) ∨ (¬ p544)) : (¬ p14) ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p301) ∨ (¬ p351) ∨ (¬ p544) := by
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
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12787 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17713 (p7 p16 p71 p185 p423 p980 p1115 p1324 p1708 p1710 p1805 : Prop)
    (h16152 : (¬ p7))
    (h16309 : (¬ p1324))
    (h10766 : p1708)
    (h12788 : p7 ∨ (¬ p16) ∨ (¬ p71) ∨ (¬ p185) ∨ (¬ p423) ∨ (¬ p980) ∨ (¬ p1115) ∨ p1324 ∨ (¬ p1708) ∨ (¬ p1710) ∨ (¬ p1805)) : (¬ p16) ∨ (¬ p71) ∨ (¬ p185) ∨ (¬ p423) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p1710) ∨ (¬ p1805) := by
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
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1805 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p1324) := by
    exact h16309
  have u10 : p1708 := by
    exact h10766
  rcases h12788 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step17714 (p7 p15 p16 p185 p980 p1115 p1469 p1712 : Prop)
    (h16152 : (¬ p7))
    (h12789 : p7 ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p185) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p1469) ∨ (¬ p1712)) : (¬ p15) ∨ (¬ p16) ∨ (¬ p185) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p1469) ∨ (¬ p1712) := by
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
  have u2 : p185 := by
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
  rcases h12789 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17715 (p7 p344 p406 p638 p656 p898 p1287 : Prop)
    (h16152 : (¬ p7))
    (h12790 : p7 ∨ (¬ p344) ∨ (¬ p406) ∨ (¬ p638) ∨ (¬ p656) ∨ (¬ p898) ∨ (¬ p1287)) : (¬ p344) ∨ (¬ p406) ∨ (¬ p638) ∨ (¬ p656) ∨ (¬ p898) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p638 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p656 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p898 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12790 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17716 (p7 p15 p305 p344 p423 p500 p710 p1040 p1076 : Prop)
    (h16152 : (¬ p7))
    (h12791 : p7 ∨ (¬ p15) ∨ (¬ p305) ∨ (¬ p344) ∨ (¬ p423) ∨ (¬ p500) ∨ (¬ p710) ∨ (¬ p1040) ∨ (¬ p1076)) : (¬ p15) ∨ (¬ p305) ∨ (¬ p344) ∨ (¬ p423) ∨ (¬ p500) ∨ (¬ p710) ∨ (¬ p1040) ∨ (¬ p1076) := by
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
  have u2 : p344 := by
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
  have u5 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1040 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12791 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17717 (p7 p160 p172 p1037 p1057 p1116 p1465 : Prop)
    (h16152 : (¬ p7))
    (h12792 : p7 ∨ (¬ p160) ∨ (¬ p172) ∨ (¬ p1037) ∨ (¬ p1057) ∨ (¬ p1116) ∨ (¬ p1465)) : (¬ p160) ∨ (¬ p172) ∨ (¬ p1037) ∨ (¬ p1057) ∨ (¬ p1116) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1037 := by
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
  have u5 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12792 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17718 (p7 p15 p304 p423 p500 p726 p985 p1035 : Prop)
    (h16152 : (¬ p7))
    (h12795 : p7 ∨ (¬ p15) ∨ (¬ p304) ∨ (¬ p423) ∨ (¬ p500) ∨ (¬ p726) ∨ (¬ p985) ∨ (¬ p1035)) : (¬ p15) ∨ (¬ p304) ∨ (¬ p423) ∨ (¬ p500) ∨ (¬ p726) ∨ (¬ p985) ∨ (¬ p1035) := by
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
  have u2 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p500 := by
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
  have u6 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12795 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17719 (p3 p7 p43 p135 p187 p229 p581 : Prop)
    (h16152 : (¬ p7))
    (h12796 : (¬ p3) ∨ p7 ∨ (¬ p43) ∨ (¬ p135) ∨ (¬ p187) ∨ (¬ p229) ∨ (¬ p581)) : (¬ p3) ∨ (¬ p43) ∨ (¬ p135) ∨ (¬ p187) ∨ (¬ p229) ∨ (¬ p581) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12796 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17720 (p3 p7 p71 p229 p234 p256 p576 p792 p803 p814 p1136 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16259 : (¬ p1136))
    (h12797 : (¬ p3) ∨ p7 ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p234) ∨ (¬ p256) ∨ (¬ p576) ∨ (¬ p792) ∨ (¬ p803) ∨ (¬ p814) ∨ p1136) : (¬ p3) ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p234) ∨ (¬ p256) ∨ (¬ p576) ∨ (¬ p803) ∨ (¬ p814) := by
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
  have u4 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p803 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p792 := by
    exact h4535
  have u10 : (¬ p1136) := by
    exact h16259
  rcases h12797 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (u10 q10)

theorem step17721 (p7 p15 p16 p185 p423 p985 p1035 p1584 : Prop)
    (h16152 : (¬ p7))
    (h12798 : p7 ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p185) ∨ (¬ p423) ∨ (¬ p985) ∨ (¬ p1035) ∨ (¬ p1584)) : (¬ p15) ∨ (¬ p16) ∨ (¬ p185) ∨ (¬ p423) ∨ (¬ p985) ∨ (¬ p1035) ∨ (¬ p1584) := by
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
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p423 := by
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
  have u6 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12798 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17722 (p7 p15 p101 p124 p423 p788 p1035 p1136 p1454 p1624 : Prop)
    (h16152 : (¬ p7))
    (h5066 : p788)
    (h16259 : (¬ p1136))
    (h12799 : p7 ∨ (¬ p15) ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p423) ∨ (¬ p788) ∨ (¬ p1035) ∨ p1136 ∨ (¬ p1454) ∨ (¬ p1624)) : (¬ p15) ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p423) ∨ (¬ p1035) ∨ (¬ p1454) ∨ (¬ p1624) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
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
  have u3 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1454 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p788 := by
    exact h5066
  have u9 : (¬ p1136) := by
    exact h16259
  rcases h12799 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u4)
  · exact False.elim (u9 q7)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step17724 (p7 p15 p19 p102 p290 p1055 p1103 p1116 : Prop)
    (h16152 : (¬ p7))
    (h12802 : p7 ∨ (¬ p15) ∨ (¬ p19) ∨ (¬ p102) ∨ (¬ p290) ∨ (¬ p1055) ∨ (¬ p1103) ∨ (¬ p1116)) : (¬ p15) ∨ (¬ p19) ∨ (¬ p102) ∨ (¬ p290) ∨ (¬ p1055) ∨ (¬ p1103) ∨ (¬ p1116) := by
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
  have u2 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p290 := by
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
  rcases h12802 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17725 (p7 p16 p18 p71 p127 p185 p234 p542 p667 p1115 : Prop)
    (h16152 : (¬ p7))
    (h12804 : p7 ∨ (¬ p16) ∨ (¬ p18) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p185) ∨ (¬ p234) ∨ (¬ p542) ∨ (¬ p667) ∨ (¬ p1115)) : (¬ p16) ∨ (¬ p18) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p185) ∨ (¬ p234) ∨ (¬ p542) ∨ (¬ p667) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p18 := by
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
  have u4 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h12804 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17726 (p3 p105 p133 p788 : Prop)
    (h16157 : (¬ p133))
    (h5066 : p788)
    (h12805 : (¬ p3) ∨ p105 ∨ p133 ∨ (¬ p788)) : (¬ p3) ∨ p105 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p105) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p133) := by
    exact h16157
  have u3 : p788 := by
    exact h5066
  rcases h12805 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)

theorem step17727 (p7 p41 p63 p304 p346 p424 p500 p542 : Prop)
    (h16152 : (¬ p7))
    (h12808 : p7 ∨ (¬ p41) ∨ (¬ p63) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p424) ∨ (¬ p500) ∨ (¬ p542)) : (¬ p41) ∨ (¬ p63) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p424) ∨ (¬ p500) ∨ (¬ p542) := by
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
  have u2 : p304 := by
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
  have u5 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12808 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17728 (p7 p125 p327 p435 p441 p1631 : Prop)
    (h16152 : (¬ p7))
    (h12809 : p7 ∨ (¬ p125) ∨ (¬ p327) ∨ (¬ p435) ∨ (¬ p441) ∨ (¬ p1631)) : (¬ p125) ∨ (¬ p327) ∨ (¬ p435) ∨ (¬ p441) ∨ (¬ p1631) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p441 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1631 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12809 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17730 (p7 p90 p193 p419 p542 p789 p795 p836 p918 : Prop)
    (h16152 : (¬ p7))
    (h12811 : p7 ∨ (¬ p90) ∨ (¬ p193) ∨ (¬ p419) ∨ (¬ p542) ∨ (¬ p789) ∨ (¬ p795) ∨ (¬ p836) ∨ (¬ p918)) : (¬ p90) ∨ (¬ p193) ∨ (¬ p419) ∨ (¬ p542) ∨ (¬ p789) ∨ (¬ p795) ∨ (¬ p836) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p795 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12811 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17732 (p7 p45 p89 p132 p193 p304 p346 p430 p500 p581 p734 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16180 : (¬ p430))
    (h12813 : p7 ∨ (¬ p45) ∨ (¬ p89) ∨ (¬ p132) ∨ (¬ p193) ∨ (¬ p304) ∨ (¬ p346) ∨ p430 ∨ (¬ p500) ∨ (¬ p581) ∨ (¬ p734)) : (¬ p45) ∨ (¬ p89) ∨ (¬ p193) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p500) ∨ (¬ p581) ∨ (¬ p734) := by
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
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p132 := by
    exact h786
  have u10 : (¬ p430) := by
    exact h16180
  rcases h12813 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u10 q7)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step17733 (p7 p41 p63 p142 p304 p346 p430 p500 p734 p788 : Prop)
    (h16152 : (¬ p7))
    (h16180 : (¬ p430))
    (h5066 : p788)
    (h12814 : p7 ∨ (¬ p41) ∨ (¬ p63) ∨ (¬ p142) ∨ (¬ p304) ∨ (¬ p346) ∨ p430 ∨ (¬ p500) ∨ (¬ p734) ∨ (¬ p788)) : (¬ p41) ∨ (¬ p63) ∨ (¬ p142) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p500) ∨ (¬ p734) := by
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
  have u2 : p142 := by
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
  have u5 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p430) := by
    exact h16180
  have u9 : p788 := by
    exact h5066
  rcases h12814 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u8 q6)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u9)

theorem step17734 (p7 p15 p304 p346 p419 p500 p542 p1193 p1286 : Prop)
    (h16152 : (¬ p7))
    (h12815 : p7 ∨ (¬ p15) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p419) ∨ (¬ p500) ∨ (¬ p542) ∨ (¬ p1193) ∨ (¬ p1286)) : (¬ p15) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p419) ∨ (¬ p500) ∨ (¬ p542) ∨ (¬ p1193) ∨ (¬ p1286) := by
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
  have u2 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
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
  have u6 : p1193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12815 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17735 (p7 p45 p89 p193 p304 p346 p500 p838 p1393 : Prop)
    (h16152 : (¬ p7))
    (h12816 : p7 ∨ (¬ p45) ∨ (¬ p89) ∨ (¬ p193) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p500) ∨ (¬ p838) ∨ (¬ p1393)) : (¬ p45) ∨ (¬ p89) ∨ (¬ p193) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p500) ∨ (¬ p838) ∨ (¬ p1393) := by
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
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p838 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12816 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17737 (p7 p101 p124 p532 p788 p961 p1324 : Prop)
    (h16152 : (¬ p7))
    (h5066 : p788)
    (h16309 : (¬ p1324))
    (h12818 : p7 ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p532) ∨ (¬ p788) ∨ (¬ p961) ∨ p1324) : (¬ p101) ∨ (¬ p124) ∨ (¬ p532) ∨ (¬ p961) := by
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
  have u5 : p788 := by
    exact h5066
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h12818 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step17739 (p7 p256 p576 p686 p792 p1077 p1118 p1349 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h4535 : p792)
    (h12822 : p7 ∨ (¬ p256) ∨ (¬ p576) ∨ p686 ∨ (¬ p792) ∨ (¬ p1077) ∨ (¬ p1118) ∨ (¬ p1349)) : (¬ p256) ∨ (¬ p576) ∨ (¬ p1077) ∨ (¬ p1118) ∨ (¬ p1349) := by
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
  have u2 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1118 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p686) := by
    exact h16205
  have u7 : p792 := by
    exact h4535
  rcases h12822 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17740 (p7 p124 p125 p164 p280 p1036 p1077 : Prop)
    (h16152 : (¬ p7))
    (h789 : p164)
    (h16173 : (¬ p280))
    (h12823 : p7 ∨ (¬ p124) ∨ (¬ p125) ∨ (¬ p164) ∨ p280 ∨ (¬ p1036) ∨ (¬ p1077)) : (¬ p124) ∨ (¬ p125) ∨ (¬ p1036) ∨ (¬ p1077) := by
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
  have u5 : p164 := by
    exact h789
  have u6 : (¬ p280) := by
    exact h16173
  rcases h12823 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17741 (p7 p419 p803 p814 p861 p1346 : Prop)
    (h16152 : (¬ p7))
    (h12824 : p7 ∨ (¬ p419) ∨ (¬ p803) ∨ (¬ p814) ∨ (¬ p861) ∨ (¬ p1346)) : (¬ p419) ∨ (¬ p803) ∨ (¬ p814) ∨ (¬ p861) ∨ (¬ p1346) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p803 := by
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
  rcases h12824 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17742 (p7 p17 p190 p301 p351 p662 p980 p1035 p1140 : Prop)
    (h16152 : (¬ p7))
    (h12826 : p7 ∨ (¬ p17) ∨ (¬ p190) ∨ (¬ p301) ∨ (¬ p351) ∨ (¬ p662) ∨ (¬ p980) ∨ (¬ p1035) ∨ (¬ p1140)) : (¬ p17) ∨ (¬ p190) ∨ (¬ p301) ∨ (¬ p351) ∨ (¬ p662) ∨ (¬ p980) ∨ (¬ p1035) ∨ (¬ p1140) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p190 := by
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
  have u4 : p662 := by
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
  have u7 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12826 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17743 (p3 p7 p11 p17 p190 p532 p533 p534 : Prop)
    (h16152 : (¬ p7))
    (h12827 : (¬ p3) ∨ p7 ∨ (¬ p11) ∨ (¬ p17) ∨ (¬ p190) ∨ (¬ p532) ∨ (¬ p533) ∨ (¬ p534)) : (¬ p3) ∨ (¬ p11) ∨ (¬ p17) ∨ (¬ p190) ∨ (¬ p532) ∨ (¬ p533) ∨ (¬ p534) := by
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
  have u4 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12827 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17744 (p7 p17 p239 p301 p351 p536 p544 p940 : Prop)
    (h16152 : (¬ p7))
    (h12828 : p7 ∨ (¬ p17) ∨ (¬ p239) ∨ (¬ p301) ∨ (¬ p351) ∨ (¬ p536) ∨ (¬ p544) ∨ (¬ p940)) : (¬ p17) ∨ (¬ p239) ∨ (¬ p301) ∨ (¬ p351) ∨ (¬ p536) ∨ (¬ p544) ∨ (¬ p940) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p239 := by
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
  have u4 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12828 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17745 (p7 p261 p288 p301 p304 p327 p406 p419 p817 : Prop)
    (h16152 : (¬ p7))
    (h12829 : p7 ∨ (¬ p261) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p304) ∨ (¬ p327) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p817)) : (¬ p261) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p304) ∨ (¬ p327) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p817) := by
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
  have u5 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p817 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12829 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17746 (p7 p17 p258 p346 p406 p419 p542 p817 : Prop)
    (h16152 : (¬ p7))
    (h12830 : p7 ∨ (¬ p17) ∨ (¬ p258) ∨ (¬ p346) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p542) ∨ (¬ p817)) : (¬ p17) ∨ (¬ p258) ∨ (¬ p346) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p542) ∨ (¬ p817) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p817 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12830 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17747 (p7 p135 p185 p187 p255 p256 p346 p406 p419 p475 p542 : Prop)
    (h16152 : (¬ p7))
    (h12831 : p7 ∨ (¬ p135) ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p255) ∨ (¬ p256) ∨ (¬ p346) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p475) ∨ (¬ p542)) : (¬ p135) ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p255) ∨ (¬ p256) ∨ (¬ p346) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p475) ∨ (¬ p542) := by
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
  have u2 : p187 := by
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
  have u5 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p475 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h12831 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step17749 (p63 p582 p1136 p1530 : Prop)
    (h16259 : (¬ p1136))
    (h9352 : p1530)
    (h12834 : (¬ p63) ∨ p582 ∨ p1136 ∨ (¬ p1530)) : (¬ p63) ∨ p582 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p582) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p1136) := by
    exact h16259
  have u3 : p1530 := by
    exact h9352
  rcases h12834 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)

theorem step17750 (p7 p84 p193 p419 p499 p582 p616 p789 p795 p1195 : Prop)
    (h16152 : (¬ p7))
    (h12835 : p7 ∨ (¬ p84) ∨ (¬ p193) ∨ (¬ p419) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p616) ∨ (¬ p789) ∨ (¬ p795) ∨ (¬ p1195)) : (¬ p84) ∨ (¬ p193) ∨ (¬ p419) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p616) ∨ (¬ p789) ∨ (¬ p795) ∨ (¬ p1195) := by
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
  have u2 : p419 := by
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
  have u5 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p795 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h12835 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17753 (p7 p435 p616 p1195 p1548 p1674 : Prop)
    (h16152 : (¬ p7))
    (h12838 : p7 ∨ (¬ p435) ∨ (¬ p616) ∨ (¬ p1195) ∨ (¬ p1548) ∨ (¬ p1674)) : (¬ p435) ∨ (¬ p616) ∨ (¬ p1195) ∨ (¬ p1548) ∨ (¬ p1674) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1548 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1674 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12838 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17755 (p7 p44 p63 p69 p1257 p1273 : Prop)
    (h16152 : (¬ p7))
    (h12840 : p7 ∨ (¬ p44) ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p1257) ∨ (¬ p1273)) : (¬ p44) ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p1257) ∨ (¬ p1273) := by
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
  have u3 : p1257 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12840 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17756 (p7 p419 p595 p685 p1136 p1286 p1366 : Prop)
    (h16152 : (¬ p7))
    (h3898 : p685)
    (h16259 : (¬ p1136))
    (h12841 : p7 ∨ (¬ p419) ∨ (¬ p595) ∨ (¬ p685) ∨ p1136 ∨ (¬ p1286) ∨ (¬ p1366)) : (¬ p419) ∨ (¬ p595) ∨ (¬ p1286) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p685 := by
    exact h3898
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h12841 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17757 (p7 p8 p303 p312 p345 p657 : Prop)
    (h16152 : (¬ p7))
    (h12842 : p7 ∨ (¬ p8) ∨ (¬ p303) ∨ (¬ p312) ∨ (¬ p345) ∨ (¬ p657)) : (¬ p8) ∨ (¬ p303) ∨ (¬ p312) ∨ (¬ p345) ∨ (¬ p657) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p312 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12842 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17758 (p7 p106 p225 p348 p601 p636 : Prop)
    (h16152 : (¬ p7))
    (h12843 : p7 ∨ (¬ p106) ∨ (¬ p225) ∨ (¬ p348) ∨ (¬ p601) ∨ (¬ p636)) : (¬ p106) ∨ (¬ p225) ∨ (¬ p348) ∨ (¬ p601) ∨ (¬ p636) := by
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
  have u2 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12843 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17759 (p7 p18 p127 p133 p233 p419 p1193 p1286 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h2345 : p233)
    (h12844 : p7 ∨ (¬ p18) ∨ (¬ p127) ∨ p133 ∨ (¬ p233) ∨ (¬ p419) ∨ (¬ p1193) ∨ (¬ p1286)) : (¬ p18) ∨ (¬ p127) ∨ (¬ p419) ∨ (¬ p1193) ∨ (¬ p1286) := by
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
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p133) := by
    exact h16157
  have u7 : p233 := by
    exact h2345
  rcases h12844 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17761 (p7 p90 p186 p406 p475 p858 p1385 : Prop)
    (h16152 : (¬ p7))
    (h12847 : p7 ∨ (¬ p90) ∨ (¬ p186) ∨ (¬ p406) ∨ (¬ p475) ∨ (¬ p858) ∨ (¬ p1385)) : (¬ p90) ∨ (¬ p186) ∨ (¬ p406) ∨ (¬ p475) ∨ (¬ p858) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p475 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12847 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17762 (p7 p41 p63 p424 p685 p1136 p1366 : Prop)
    (h16152 : (¬ p7))
    (h3898 : p685)
    (h16259 : (¬ p1136))
    (h12848 : p7 ∨ (¬ p41) ∨ (¬ p63) ∨ (¬ p424) ∨ (¬ p685) ∨ p1136 ∨ (¬ p1366)) : (¬ p41) ∨ (¬ p63) ∨ (¬ p424) ∨ (¬ p1366) := by
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
  have u2 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p685 := by
    exact h3898
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h12848 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step17763 (p7 p84 p186 p346 p406 p426 p475 p582 p634 p685 p756 p801 p858 p1366 p1538 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h3898 : p685)
    (h12849 : p7 ∨ (¬ p84) ∨ (¬ p186) ∨ (¬ p346) ∨ (¬ p406) ∨ p426 ∨ (¬ p475) ∨ (¬ p582) ∨ (¬ p634) ∨ (¬ p685) ∨ (¬ p756) ∨ (¬ p801) ∨ (¬ p858) ∨ (¬ p1366) ∨ (¬ p1538)) : (¬ p84) ∨ (¬ p186) ∨ (¬ p346) ∨ (¬ p406) ∨ (¬ p475) ∨ (¬ p582) ∨ (¬ p634) ∨ (¬ p756) ∨ (¬ p801) ∨ (¬ p858) ∨ (¬ p1366) ∨ (¬ p1538) := by
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
  have u2 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p475 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p634 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p801 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))
  have u12 : (¬ p7) := by
    exact h16152
  have u13 : (¬ p426) := by
    exact h16178
  have u14 : p685 := by
    exact h3898
  rcases h12849 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14
  · exact False.elim (u12 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u13 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u14)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)
  · exact False.elim (q12 u9)
  · exact False.elim (q13 u10)
  · exact False.elim (q14 u11)

theorem step17764 (p4 p7 p288 p301 p738 p756 : Prop)
    (h16152 : (¬ p7))
    (h12850 : (¬ p4) ∨ p7 ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p738) ∨ (¬ p756)) : (¬ p4) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p738) ∨ (¬ p756) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p4 := by
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
  rcases h12850 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17765 (p7 p346 p426 p756 p792 p918 p1584 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h4535 : p792)
    (h12851 : p7 ∨ (¬ p346) ∨ p426 ∨ (¬ p756) ∨ (¬ p792) ∨ (¬ p918) ∨ (¬ p1584)) : (¬ p346) ∨ (¬ p756) ∨ (¬ p918) ∨ (¬ p1584) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p426) := by
    exact h16178
  have u6 : p792 := by
    exact h4535
  rcases h12851 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17766 (p7 p40 p69 p101 p499 p633 p788 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h5066 : p788)
    (h12852 : p7 ∨ p40 ∨ (¬ p69) ∨ (¬ p101) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p788)) : (¬ p69) ∨ (¬ p101) ∨ (¬ p499) ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p40) := by
    exact h16150
  have u6 : p788 := by
    exact h5066
  rcases h12852 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17767 (p7 p419 p685 p789 p790 p791 p1366 : Prop)
    (h16152 : (¬ p7))
    (h3898 : p685)
    (h16213 : (¬ p791))
    (h12853 : p7 ∨ (¬ p419) ∨ (¬ p685) ∨ (¬ p789) ∨ (¬ p790) ∨ p791 ∨ (¬ p1366)) : (¬ p419) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p419 := by
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
  have u3 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p685 := by
    exact h3898
  have u6 : (¬ p791) := by
    exact h16213
  rcases h12853 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step17769 (p7 p362 p420 p633 p961 p1075 p1445 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16350 : (¬ p1445))
    (h12858 : p7 ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p633) ∨ (¬ p961) ∨ (¬ p1075) ∨ p1445) : (¬ p362) ∨ (¬ p420) ∨ (¬ p633) ∨ (¬ p961) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p362 := by
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
  have u3 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p1075 := by
    exact h6478
  have u6 : (¬ p1445) := by
    exact h16350
  rcases h12858 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)

theorem step17770 (p7 p15 p19 p980 p1055 p1103 p1449 p1665 : Prop)
    (h16152 : (¬ p7))
    (h12859 : p7 ∨ (¬ p15) ∨ (¬ p19) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1103) ∨ (¬ p1449) ∨ (¬ p1665)) : (¬ p15) ∨ (¬ p19) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1103) ∨ (¬ p1449) ∨ (¬ p1665) := by
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
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12859 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17771 (p7 p323 p370 p437 p687 p1666 : Prop)
    (h16152 : (¬ p7))
    (h12860 : p7 ∨ (¬ p323) ∨ (¬ p370) ∨ (¬ p437) ∨ (¬ p687) ∨ (¬ p1666)) : (¬ p323) ∨ (¬ p370) ∨ (¬ p437) ∨ (¬ p687) ∨ (¬ p1666) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p370 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p437 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12860 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17772 (p7 p213 p324 p362 p387 p419 : Prop)
    (h16152 : (¬ p7))
    (h12861 : p7 ∨ (¬ p213) ∨ (¬ p324) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p419)) : (¬ p213) ∨ (¬ p324) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p324 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p362 := by
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
  rcases h12861 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17773 (p7 p45 p171 p927 p1562 p1584 : Prop)
    (h16152 : (¬ p7))
    (h12862 : p7 ∨ (¬ p45) ∨ (¬ p171) ∨ (¬ p927) ∨ (¬ p1562) ∨ (¬ p1584)) : (¬ p45) ∨ (¬ p171) ∨ (¬ p927) ∨ (¬ p1562) ∨ (¬ p1584) := by
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
  have u2 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12862 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17774 (p7 p18 p127 p171 p187 p234 p237 p803 p814 : Prop)
    (h16152 : (¬ p7))
    (h12863 : p7 ∨ (¬ p18) ∨ (¬ p127) ∨ (¬ p171) ∨ (¬ p187) ∨ (¬ p234) ∨ (¬ p237) ∨ (¬ p803) ∨ (¬ p814)) : (¬ p18) ∨ (¬ p127) ∨ (¬ p171) ∨ (¬ p187) ∨ (¬ p234) ∨ (¬ p237) ∨ (¬ p803) ∨ (¬ p814) := by
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
  have u2 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p803 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12863 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17775 (p7 p370 p381 p406 p532 p1333 : Prop)
    (h16152 : (¬ p7))
    (h12864 : p7 ∨ (¬ p370) ∨ (¬ p381) ∨ (¬ p406) ∨ (¬ p532) ∨ (¬ p1333)) : (¬ p370) ∨ (¬ p381) ∨ (¬ p406) ∨ (¬ p532) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p370 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p381 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12864 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17776 (p7 p68 p121 p127 p885 p985 p1096 p1452 p1567 p1667 : Prop)
    (h16152 : (¬ p7))
    (h12866 : p7 ∨ (¬ p68) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p885) ∨ (¬ p985) ∨ (¬ p1096) ∨ (¬ p1452) ∨ (¬ p1567) ∨ (¬ p1667)) : (¬ p68) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p885) ∨ (¬ p985) ∨ (¬ p1096) ∨ (¬ p1452) ∨ (¬ p1567) ∨ (¬ p1667) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p68 := by
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
  have u3 : p885 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1567 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1667 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h12866 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17777 (p7 p70 p121 p127 p985 p1099 p1452 p1538 : Prop)
    (h16152 : (¬ p7))
    (h12867 : p7 ∨ (¬ p70) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p985) ∨ (¬ p1099) ∨ (¬ p1452) ∨ (¬ p1538)) : (¬ p70) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p985) ∨ (¬ p1099) ∨ (¬ p1452) ∨ (¬ p1538) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p70 := by
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
  have u3 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12867 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17778 (p7 p15 p19 p121 p1136 p1386 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16259 : (¬ p1136))
    (h8348 : p1386)
    (h12868 : p7 ∨ (¬ p15) ∨ (¬ p19) ∨ (¬ p121) ∨ p1136 ∨ (¬ p1386) ∨ (¬ p1452)) : (¬ p15) ∨ (¬ p19) ∨ (¬ p121) ∨ (¬ p1452) := by
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
  have u2 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p1136) := by
    exact h16259
  have u6 : p1386 := by
    exact h8348
  rcases h12868 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step17780 (p7 p129 p189 p233 p256 p419 p519 p789 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h2345 : p233)
    (h12870 : p7 ∨ p129 ∨ (¬ p189) ∨ (¬ p233) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p519) ∨ (¬ p789)) : (¬ p189) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p519) ∨ (¬ p789) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p519 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p233 := by
    exact h2345
  rcases h12870 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17782 (p7 p72 p211 p368 p406 p419 p1187 : Prop)
    (h16152 : (¬ p7))
    (h12872 : p7 ∨ (¬ p72) ∨ (¬ p211) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p1187)) : (¬ p72) ∨ (¬ p211) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p211 := by
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
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12872 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17783 (p7 p39 p68 p88 p185 p211 p368 p406 p419 p739 p1366 p1584 : Prop)
    (h16152 : (¬ p7))
    (h12873 : p7 ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p185) ∨ (¬ p211) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p739) ∨ (¬ p1366) ∨ (¬ p1584)) : (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p185) ∨ (¬ p211) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p739) ∨ (¬ p1366) ∨ (¬ p1584) := by
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
  have u4 : p211 := by
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
  have u7 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p739 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : (¬ p7) := by
    exact h16152
  rcases h12873 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
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

theorem step17784 (p7 p45 p193 p685 p791 p801 p1366 p1393 : Prop)
    (h16152 : (¬ p7))
    (h3898 : p685)
    (h16213 : (¬ p791))
    (h12875 : p7 ∨ (¬ p45) ∨ (¬ p193) ∨ (¬ p685) ∨ p791 ∨ (¬ p801) ∨ (¬ p1366) ∨ (¬ p1393)) : (¬ p45) ∨ (¬ p193) ∨ (¬ p801) ∨ (¬ p1366) ∨ (¬ p1393) := by
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
  have u2 : p801 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p685 := by
    exact h3898
  have u7 : (¬ p791) := by
    exact h16213
  rcases h12875 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17785 (p7 p17 p237 p286 p301 p342 : Prop)
    (h16152 : (¬ p7))
    (h12878 : p7 ∨ (¬ p17) ∨ (¬ p237) ∨ (¬ p286) ∨ (¬ p301) ∨ (¬ p342)) : (¬ p17) ∨ (¬ p237) ∨ (¬ p286) ∨ (¬ p301) ∨ (¬ p342) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p342 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12878 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17786 (p7 p45 p101 p124 p129 p262 p581 p788 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h5066 : p788)
    (h12879 : p7 ∨ (¬ p45) ∨ (¬ p101) ∨ (¬ p124) ∨ p129 ∨ (¬ p262) ∨ (¬ p581) ∨ (¬ p788)) : (¬ p45) ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p262) ∨ (¬ p581) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
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
  have u3 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p788 := by
    exact h5066
  rcases h12879 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step17787 (p7 p213 p324 p362 p434 p435 : Prop)
    (h16152 : (¬ p7))
    (h12880 : p7 ∨ (¬ p213) ∨ (¬ p324) ∨ (¬ p362) ∨ (¬ p434) ∨ (¬ p435)) : (¬ p213) ∨ (¬ p324) ∨ (¬ p362) ∨ (¬ p434) ∨ (¬ p435) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p324 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12880 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17788 (p7 p101 p323 p387 p633 p1135 p1160 : Prop)
    (h16152 : (¬ p7))
    (h6744 : p1135)
    (h16265 : (¬ p1160))
    (h12882 : p7 ∨ (¬ p101) ∨ (¬ p323) ∨ (¬ p387) ∨ (¬ p633) ∨ (¬ p1135) ∨ p1160) : (¬ p101) ∨ (¬ p323) ∨ (¬ p387) ∨ (¬ p633) := by
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
  have u2 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p1135 := by
    exact h6744
  have u6 : (¬ p1160) := by
    exact h16265
  rcases h12882 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)

theorem step17789 (p7 p39 p63 p68 p327 p406 p419 p420 p475 p495 : Prop)
    (h16152 : (¬ p7))
    (h12883 : p7 ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p327) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p420) ∨ (¬ p475) ∨ (¬ p495)) : (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p327) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p420) ∨ (¬ p475) ∨ (¬ p495) := by
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
  have u3 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p475 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h12883 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17790 (p7 p406 p617 p739 p801 p858 p1099 p1366 p1538 : Prop)
    (h16152 : (¬ p7))
    (h12884 : p7 ∨ (¬ p406) ∨ (¬ p617) ∨ (¬ p739) ∨ (¬ p801) ∨ (¬ p858) ∨ (¬ p1099) ∨ (¬ p1366) ∨ (¬ p1538)) : (¬ p406) ∨ (¬ p617) ∨ (¬ p739) ∨ (¬ p801) ∨ (¬ p858) ∨ (¬ p1099) ∨ (¬ p1366) ∨ (¬ p1538) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p739 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p801 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12884 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17791 (p7 p132 p258 p280 p420 p640 p726 p1562 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16173 : (¬ p280))
    (h12885 : p7 ∨ (¬ p132) ∨ (¬ p258) ∨ p280 ∨ (¬ p420) ∨ (¬ p640) ∨ (¬ p726) ∨ (¬ p1562)) : (¬ p258) ∨ (¬ p420) ∨ (¬ p640) ∨ (¬ p726) ∨ (¬ p1562) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p640 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p132 := by
    exact h786
  have u7 : (¬ p280) := by
    exact h16173
  rcases h12885 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (u7 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17792 (p7 p124 p132 p193 p258 p751 p791 p985 p1035 p1256 p1624 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16213 : (¬ p791))
    (h12886 : p7 ∨ (¬ p124) ∨ (¬ p132) ∨ (¬ p193) ∨ (¬ p258) ∨ (¬ p751) ∨ p791 ∨ (¬ p985) ∨ (¬ p1035) ∨ (¬ p1256) ∨ (¬ p1624)) : (¬ p124) ∨ (¬ p193) ∨ (¬ p258) ∨ (¬ p751) ∨ (¬ p985) ∨ (¬ p1035) ∨ (¬ p1256) ∨ (¬ p1624) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p751 := by
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
  have u6 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p132 := by
    exact h786
  have u10 : (¬ p791) := by
    exact h16213
  rcases h12886 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u10 q6)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step17795 (p7 p101 p141 p193 p288 p323 p427 p791 : Prop)
    (h16152 : (¬ p7))
    (h2334 : p427)
    (h16213 : (¬ p791))
    (h12890 : p7 ∨ (¬ p101) ∨ (¬ p141) ∨ (¬ p193) ∨ (¬ p288) ∨ (¬ p323) ∨ (¬ p427) ∨ p791) : (¬ p101) ∨ (¬ p141) ∨ (¬ p193) ∨ (¬ p288) ∨ (¬ p323) := by
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
  have u2 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p427 := by
    exact h2334
  have u7 : (¬ p791) := by
    exact h16213
  rcases h12890 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u6)
  · exact False.elim (u7 q7)

theorem step17796 (p7 p124 p233 p258 p419 p519 p658 p789 : Prop)
    (h16152 : (¬ p7))
    (h2345 : p233)
    (h16199 : (¬ p658))
    (h12891 : p7 ∨ (¬ p124) ∨ (¬ p233) ∨ (¬ p258) ∨ (¬ p419) ∨ (¬ p519) ∨ p658 ∨ (¬ p789)) : (¬ p124) ∨ (¬ p258) ∨ (¬ p419) ∨ (¬ p519) ∨ (¬ p789) := by
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
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p519 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p233 := by
    exact h2345
  have u7 : (¬ p658) := by
    exact h16199
  rcases h12891 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step17797 (p7 p163 p193 p406 p534 p690 p735 p791 p858 p876 : Prop)
    (h16152 : (¬ p7))
    (h16213 : (¬ p791))
    (h5054 : p876)
    (h12892 : p7 ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p406) ∨ (¬ p534) ∨ (¬ p690) ∨ (¬ p735) ∨ p791 ∨ (¬ p858) ∨ (¬ p876)) : (¬ p163) ∨ (¬ p193) ∨ (¬ p406) ∨ (¬ p534) ∨ (¬ p690) ∨ (¬ p735) ∨ (¬ p858) := by
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
  have u2 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p735 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p791) := by
    exact h16213
  have u9 : p876 := by
    exact h5054
  rcases h12892 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u8 q7)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u9)

theorem step17798 (p7 p86 p142 p161 p193 p1232 p1449 p1665 : Prop)
    (h16152 : (¬ p7))
    (h12893 : p7 ∨ (¬ p86) ∨ (¬ p142) ∨ (¬ p161) ∨ (¬ p193) ∨ (¬ p1232) ∨ (¬ p1449) ∨ (¬ p1665)) : (¬ p86) ∨ (¬ p142) ∨ (¬ p161) ∨ (¬ p193) ∨ (¬ p1232) ∨ (¬ p1449) ∨ (¬ p1665) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12893 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17799 (p7 p84 p142 p193 p323 p603 p616 p929 p1096 : Prop)
    (h16152 : (¬ p7))
    (h12894 : p7 ∨ (¬ p84) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p323) ∨ (¬ p603) ∨ (¬ p616) ∨ (¬ p929) ∨ (¬ p1096)) : (¬ p84) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p323) ∨ (¬ p603) ∨ (¬ p616) ∨ (¬ p929) ∨ (¬ p1096) := by
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
  have u2 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p603 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12894 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17801 (p7 p39 p69 p406 p620 p1287 p1387 : Prop)
    (h16152 : (¬ p7))
    (h12896 : p7 ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p406) ∨ (¬ p620) ∨ (¬ p1287) ∨ (¬ p1387)) : (¬ p39) ∨ (¬ p69) ∨ (¬ p406) ∨ (¬ p620) ∨ (¬ p1287) ∨ (¬ p1387) := by
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
  have u2 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p620 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12896 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17802 (p7 p63 p616 p792 p1287 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16309 : (¬ p1324))
    (h12897 : p7 ∨ (¬ p63) ∨ (¬ p616) ∨ (¬ p792) ∨ (¬ p1287) ∨ p1324 ∨ (¬ p1325)) : (¬ p63) ∨ (¬ p616) ∨ (¬ p1287) ∨ (¬ p1325) := by
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
  have u2 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p792 := by
    exact h4535
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h12897 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step17804 (p7 p495 p639 p752 p1096 p1604 : Prop)
    (h16152 : (¬ p7))
    (h12900 : p7 ∨ (¬ p495) ∨ (¬ p639) ∨ (¬ p752) ∨ (¬ p1096) ∨ (¬ p1604)) : (¬ p495) ∨ (¬ p639) ∨ (¬ p752) ∨ (¬ p1096) ∨ (¬ p1604) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p639 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p752 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1604 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12900 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17805 (p7 p70 p127 p980 p1074 p1099 p1449 p1665 : Prop)
    (h16152 : (¬ p7))
    (h12901 : p7 ∨ (¬ p70) ∨ (¬ p127) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1449) ∨ (¬ p1665)) : (¬ p70) ∨ (¬ p127) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1449) ∨ (¬ p1665) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12901 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17808 (p7 p45 p129 p233 p406 p419 p816 p1393 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h2345 : p233)
    (h12904 : p7 ∨ (¬ p45) ∨ p129 ∨ (¬ p233) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p816) ∨ (¬ p1393)) : (¬ p45) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p816) ∨ (¬ p1393) := by
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
  have u2 : p419 := by
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
  have u7 : p233 := by
    exact h2345
  rcases h12904 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17809 (p7 p616 p840 p899 p925 p1096 : Prop)
    (h16152 : (¬ p7))
    (h12905 : p7 ∨ (¬ p616) ∨ (¬ p840) ∨ (¬ p899) ∨ (¬ p925) ∨ (¬ p1096)) : (¬ p616) ∨ (¬ p840) ∨ (¬ p899) ∨ (¬ p925) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p899 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p925 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12905 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17810 (p7 p25 p44 p171 p237 p323 p521 p814 p1611 p1666 : Prop)
    (h16152 : (¬ p7))
    (h12906 : p7 ∨ (¬ p25) ∨ (¬ p44) ∨ (¬ p171) ∨ (¬ p237) ∨ (¬ p323) ∨ (¬ p521) ∨ (¬ p814) ∨ (¬ p1611) ∨ (¬ p1666)) : (¬ p25) ∨ (¬ p44) ∨ (¬ p171) ∨ (¬ p237) ∨ (¬ p323) ∨ (¬ p521) ∨ (¬ p814) ∨ (¬ p1611) ∨ (¬ p1666) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p25 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p323 := by
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
  have u7 : p1611 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h12906 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17812 (p7 p70 p85 p101 p124 p211 p323 p521 p1385 : Prop)
    (h16152 : (¬ p7))
    (h12908 : p7 ∨ (¬ p70) ∨ (¬ p85) ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p211) ∨ (¬ p323) ∨ (¬ p521) ∨ (¬ p1385)) : (¬ p70) ∨ (¬ p85) ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p211) ∨ (¬ p323) ∨ (¬ p521) ∨ (¬ p1385) := by
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
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p521 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12908 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17813 (p7 p328 p368 p406 p419 p421 p439 p1604 : Prop)
    (h16152 : (¬ p7))
    (h12909 : p7 ∨ (¬ p328) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p421) ∨ (¬ p439) ∨ (¬ p1604)) : (¬ p328) ∨ (¬ p368) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p421) ∨ (¬ p439) ∨ (¬ p1604) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p328 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p439 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1604 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12909 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17815 (p7 p71 p121 p127 p427 p456 p601 p1136 : Prop)
    (h16152 : (¬ p7))
    (h2334 : p427)
    (h16259 : (¬ p1136))
    (h12913 : p7 ∨ (¬ p71) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p427) ∨ (¬ p456) ∨ (¬ p601) ∨ p1136) : (¬ p71) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p456) ∨ (¬ p601) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p71 := by
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
  have u6 : p427 := by
    exact h2334
  have u7 : (¬ p1136) := by
    exact h16259
  rcases h12913 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step17816 (p7 p18 p41 p63 p210 p328 p423 p424 p439 p1136 p1624 p1708 : Prop)
    (h16152 : (¬ p7))
    (h16259 : (¬ p1136))
    (h10766 : p1708)
    (h12914 : p7 ∨ (¬ p18) ∨ (¬ p41) ∨ (¬ p63) ∨ (¬ p210) ∨ (¬ p328) ∨ (¬ p423) ∨ (¬ p424) ∨ (¬ p439) ∨ p1136 ∨ (¬ p1624) ∨ (¬ p1708)) : (¬ p18) ∨ (¬ p41) ∨ (¬ p63) ∨ (¬ p210) ∨ (¬ p328) ∨ (¬ p423) ∨ (¬ p424) ∨ (¬ p439) ∨ (¬ p1624) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p328 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p439 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p1136) := by
    exact h16259
  have u11 : p1708 := by
    exact h10766
  rcases h12914 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
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

theorem step17817 (p7 p127 p133 p136 p233 p424 p1644 p1665 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h2345 : p233)
    (h12915 : p7 ∨ (¬ p127) ∨ p133 ∨ (¬ p136) ∨ (¬ p233) ∨ (¬ p424) ∨ (¬ p1644) ∨ (¬ p1665)) : (¬ p127) ∨ (¬ p136) ∨ (¬ p424) ∨ (¬ p1644) ∨ (¬ p1665) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p136 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p133) := by
    exact h16157
  have u7 : p233 := by
    exact h2345
  rcases h12915 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17818 (p7 p63 p581 p980 p1055 p1103 p1449 p1651 : Prop)
    (h16152 : (¬ p7))
    (h12916 : p7 ∨ (¬ p63) ∨ (¬ p581) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1103) ∨ (¬ p1449) ∨ (¬ p1651)) : (¬ p63) ∨ (¬ p581) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1103) ∨ (¬ p1449) ∨ (¬ p1651) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1651 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12916 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17819 (p7 p101 p124 p134 p233 p424 p658 : Prop)
    (h16152 : (¬ p7))
    (h2345 : p233)
    (h16199 : (¬ p658))
    (h12917 : p7 ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p134) ∨ (¬ p233) ∨ (¬ p424) ∨ p658) : (¬ p101) ∨ (¬ p124) ∨ (¬ p134) ∨ (¬ p424) := by
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
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p233 := by
    exact h2345
  have u6 : (¬ p658) := by
    exact h16199
  rcases h12917 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step17820 (p7 p41 p63 p163 p343 p544 p1136 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16259 : (¬ p1136))
    (h12918 : p7 ∨ (¬ p41) ∨ (¬ p63) ∨ (¬ p163) ∨ (¬ p343) ∨ (¬ p544) ∨ p1136) : (¬ p41) ∨ (¬ p63) ∨ (¬ p163) ∨ (¬ p544) := by
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
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p343 := by
    exact h1950
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h12918 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step17821 (p7 p45 p90 p127 p134 p186 : Prop)
    (h16152 : (¬ p7))
    (h12919 : p7 ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p186)) : (¬ p45) ∨ (¬ p90) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p186) := by
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
  have u2 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12919 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17822 (p7 p256 p575 p791 p928 p1537 p1604 p1651 : Prop)
    (h16152 : (¬ p7))
    (h16213 : (¬ p791))
    (h9400 : p1537)
    (h12920 : p7 ∨ (¬ p256) ∨ (¬ p575) ∨ p791 ∨ (¬ p928) ∨ (¬ p1537) ∨ (¬ p1604) ∨ (¬ p1651)) : (¬ p256) ∨ (¬ p575) ∨ (¬ p928) ∨ (¬ p1604) ∨ (¬ p1651) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p575 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1604 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1651 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p791) := by
    exact h16213
  have u7 : p1537 := by
    exact h9400
  rcases h12920 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17823 (p7 p19 p44 p102 p193 p576 p752 p791 p928 p1537 p1644 : Prop)
    (h16152 : (¬ p7))
    (h16213 : (¬ p791))
    (h9400 : p1537)
    (h12921 : p7 ∨ (¬ p19) ∨ (¬ p44) ∨ (¬ p102) ∨ (¬ p193) ∨ (¬ p576) ∨ (¬ p752) ∨ p791 ∨ (¬ p928) ∨ (¬ p1537) ∨ (¬ p1644)) : (¬ p19) ∨ (¬ p44) ∨ (¬ p102) ∨ (¬ p193) ∨ (¬ p576) ∨ (¬ p752) ∨ (¬ p928) ∨ (¬ p1644) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p44 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p752 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p791) := by
    exact h16213
  have u10 : p1537 := by
    exact h9400
  rcases h12921 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step17824 (p7 p121 p122 p499 p1136 p1611 p1666 : Prop)
    (h16152 : (¬ p7))
    (h10260 : p122)
    (h16259 : (¬ p1136))
    (h12922 : p7 ∨ (¬ p121) ∨ (¬ p122) ∨ (¬ p499) ∨ p1136 ∨ (¬ p1611) ∨ (¬ p1666)) : (¬ p121) ∨ (¬ p499) ∨ (¬ p1611) ∨ (¬ p1666) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1611 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p122 := by
    exact h10260
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h12922 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17825 (p7 p101 p256 p288 p323 p427 p791 : Prop)
    (h16152 : (¬ p7))
    (h2334 : p427)
    (h16213 : (¬ p791))
    (h12923 : p7 ∨ (¬ p101) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p323) ∨ (¬ p427) ∨ p791) : (¬ p101) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p323) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p427 := by
    exact h2334
  have u6 : (¬ p791) := by
    exact h16213
  rcases h12923 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)

theorem step17826 (p7 p18 p72 p101 p124 p211 : Prop)
    (h16152 : (¬ p7))
    (h12926 : p7 ∨ (¬ p18) ∨ (¬ p72) ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p211)) : (¬ p18) ∨ (¬ p72) ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p211) := by
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
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12926 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17828 (p7 p101 p323 p348 p726 p727 : Prop)
    (h16152 : (¬ p7))
    (h12928 : p7 ∨ (¬ p101) ∨ (¬ p323) ∨ (¬ p348) ∨ (¬ p726) ∨ (¬ p727)) : (¬ p101) ∨ (¬ p323) ∨ (¬ p348) ∨ (¬ p726) ∨ (¬ p727) := by
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
  have u2 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p727 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12928 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17829 (p7 p14 p15 p406 p534 p690 p735 p1136 p1287 p1664 : Prop)
    (h16152 : (¬ p7))
    (h16259 : (¬ p1136))
    (h10244 : p1664)
    (h12929 : p7 ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p406) ∨ (¬ p534) ∨ (¬ p690) ∨ (¬ p735) ∨ p1136 ∨ (¬ p1287) ∨ (¬ p1664)) : (¬ p14) ∨ (¬ p15) ∨ (¬ p406) ∨ (¬ p534) ∨ (¬ p690) ∨ (¬ p735) ∨ (¬ p1287) := by
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
  have u2 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p735 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p1136) := by
    exact h16259
  have u9 : p1664 := by
    exact h10244
  rcases h12929 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u8 q7)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u9)

theorem step17831 (p7 p344 p406 p663 p715 p1076 : Prop)
    (h16152 : (¬ p7))
    (h12931 : p7 ∨ (¬ p344) ∨ (¬ p406) ∨ (¬ p663) ∨ (¬ p715) ∨ (¬ p1076)) : (¬ p344) ∨ (¬ p406) ∨ (¬ p663) ∨ (¬ p715) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p663 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p715 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12931 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17832 (p7 p16 p71 p101 p124 p211 p1349 p1449 p1489 p1665 : Prop)
    (h16152 : (¬ p7))
    (h12933 : p7 ∨ (¬ p16) ∨ (¬ p71) ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p211) ∨ (¬ p1349) ∨ (¬ p1449) ∨ (¬ p1489) ∨ (¬ p1665)) : (¬ p16) ∨ (¬ p71) ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p211) ∨ (¬ p1349) ∨ (¬ p1449) ∨ (¬ p1489) ∨ (¬ p1665) := by
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
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h12933 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17833 (p7 p101 p121 p124 p263 p1226 p1347 p1442 p1508 : Prop)
    (h16152 : (¬ p7))
    (h12934 : p7 ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p124) ∨ (¬ p263) ∨ (¬ p1226) ∨ (¬ p1347) ∨ (¬ p1442) ∨ (¬ p1508)) : (¬ p101) ∨ (¬ p121) ∨ (¬ p124) ∨ (¬ p263) ∨ (¬ p1226) ∨ (¬ p1347) ∨ (¬ p1442) ∨ (¬ p1508) := by
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
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p263 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1442 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12934 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17834 (p7 p106 p883 p1077 p1096 p1232 p1307 : Prop)
    (h16152 : (¬ p7))
    (h12937 : p7 ∨ (¬ p106) ∨ (¬ p883) ∨ (¬ p1077) ∨ (¬ p1096) ∨ (¬ p1232) ∨ (¬ p1307)) : (¬ p106) ∨ (¬ p883) ∨ (¬ p1077) ∨ (¬ p1096) ∨ (¬ p1232) ∨ (¬ p1307) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1307 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12937 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17835 (p7 p39 p63 p68 p102 p161 p211 p227 p1075 p1206 p1232 p1324 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16309 : (¬ p1324))
    (h12938 : p7 ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p102) ∨ (¬ p161) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p1075) ∨ (¬ p1206) ∨ (¬ p1232) ∨ p1324) : (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p102) ∨ (¬ p161) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p1206) ∨ (¬ p1232) := by
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
  have u3 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p1075 := by
    exact h6478
  have u11 : (¬ p1324) := by
    exact h16309
  rcases h12938 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u8)
  · exact False.elim (u11 q11)

theorem step17837 (p7 p107 p419 p539 p600 p752 p1286 p1604 : Prop)
    (h16152 : (¬ p7))
    (h12941 : p7 ∨ (¬ p107) ∨ (¬ p419) ∨ (¬ p539) ∨ (¬ p600) ∨ (¬ p752) ∨ (¬ p1286) ∨ (¬ p1604)) : (¬ p107) ∨ (¬ p419) ∨ (¬ p539) ∨ (¬ p600) ∨ (¬ p752) ∨ (¬ p1286) ∨ (¬ p1604) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p539 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p600 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p752 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1604 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12941 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17838 (p7 p15 p21 p46 p142 p495 : Prop)
    (h16152 : (¬ p7))
    (h12942 : p7 ∨ (¬ p15) ∨ (¬ p21) ∨ (¬ p46) ∨ (¬ p142) ∨ (¬ p495)) : (¬ p15) ∨ (¬ p21) ∨ (¬ p46) ∨ (¬ p142) ∨ (¬ p495) := by
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
  have u2 : p46 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12942 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17839 (p7 p406 p430 p690 p928 p1287 p1387 p1537 : Prop)
    (h16152 : (¬ p7))
    (h16180 : (¬ p430))
    (h9400 : p1537)
    (h12943 : p7 ∨ (¬ p406) ∨ p430 ∨ (¬ p690) ∨ (¬ p928) ∨ (¬ p1287) ∨ (¬ p1387) ∨ (¬ p1537)) : (¬ p406) ∨ (¬ p690) ∨ (¬ p928) ∨ (¬ p1287) ∨ (¬ p1387) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p928 := by
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
  have u6 : (¬ p430) := by
    exact h16180
  have u7 : p1537 := by
    exact h9400
  rcases h12943 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step17840 (p7 p14 p18 p107 p127 p133 p343 p344 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h1950 : p343)
    (h12944 : p7 ∨ (¬ p14) ∨ (¬ p18) ∨ (¬ p107) ∨ (¬ p127) ∨ p133 ∨ (¬ p343) ∨ (¬ p344)) : (¬ p14) ∨ (¬ p18) ∨ (¬ p107) ∨ (¬ p127) ∨ (¬ p344) := by
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
  have u3 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p133) := by
    exact h16157
  have u7 : p343 := by
    exact h1950
  rcases h12944 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step17841 (p7 p16 p21 p71 p127 p533 p633 p756 p1349 p1489 : Prop)
    (h16152 : (¬ p7))
    (h12945 : p7 ∨ (¬ p16) ∨ (¬ p21) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p533) ∨ (¬ p633) ∨ (¬ p756) ∨ (¬ p1349) ∨ (¬ p1489)) : (¬ p16) ∨ (¬ p21) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p533) ∨ (¬ p633) ∨ (¬ p756) ∨ (¬ p1349) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p21 := by
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
  have u4 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h12945 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17842 (p7 p102 p127 p133 p344 p657 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h6744 : p1135)
    (h12946 : p7 ∨ (¬ p102) ∨ (¬ p127) ∨ p133 ∨ (¬ p344) ∨ (¬ p657) ∨ (¬ p1135)) : (¬ p102) ∨ (¬ p127) ∨ (¬ p344) ∨ (¬ p657) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
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
  have u5 : (¬ p133) := by
    exact h16157
  have u6 : p1135 := by
    exact h6744
  rcases h12946 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17843 (p3 p7 p133 p343 p344 p534 p726 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h1950 : p343)
    (h12947 : (¬ p3) ∨ p7 ∨ p133 ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p534) ∨ (¬ p726)) : (¬ p3) ∨ (¬ p344) ∨ (¬ p534) ∨ (¬ p726) := by
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
  have u2 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p133) := by
    exact h16157
  have u6 : p343 := by
    exact h1950
  rcases h12947 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17844 (p7 p862 p1287 p1325 p1390 p1508 : Prop)
    (h16152 : (¬ p7))
    (h12948 : p7 ∨ (¬ p862) ∨ (¬ p1287) ∨ (¬ p1325) ∨ (¬ p1390) ∨ (¬ p1508)) : (¬ p862) ∨ (¬ p1287) ∨ (¬ p1325) ∨ (¬ p1390) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p862 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1390 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12948 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17845 (p7 p102 p127 p133 p427 p601 p636 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h2334 : p427)
    (h12949 : p7 ∨ (¬ p102) ∨ (¬ p127) ∨ p133 ∨ (¬ p427) ∨ (¬ p601) ∨ (¬ p636)) : (¬ p102) ∨ (¬ p127) ∨ (¬ p601) ∨ (¬ p636) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p133) := by
    exact h16157
  have u6 : p427 := by
    exact h2334
  rcases h12949 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17846 (p7 p302 p343 p344 p639 p980 p1074 p1333 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h1950 : p343)
    (h12950 : p7 ∨ p302 ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p639) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1333)) : (¬ p344) ∨ (¬ p639) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p639 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p302) := by
    exact h16285
  have u7 : p343 := by
    exact h1950
  rcases h12950 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17847 (p2 p7 p167 p188 p263 p310 p343 p344 p424 p653 p1061 p1076 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16194 : (¬ p653))
    (h12954 : (¬ p2) ∨ p7 ∨ (¬ p167) ∨ (¬ p188) ∨ (¬ p263) ∨ (¬ p310) ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p424) ∨ p653 ∨ (¬ p1061) ∨ (¬ p1076)) : (¬ p2) ∨ (¬ p167) ∨ (¬ p188) ∨ (¬ p263) ∨ (¬ p310) ∨ (¬ p344) ∨ (¬ p424) ∨ (¬ p1061) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p263 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p343 := by
    exact h1950
  have u11 : (¬ p653) := by
    exact h16194
  rcases h12954 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u0)
  · exact False.elim (u9 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (u11 q9)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step17849 (p7 p43 p71 p481 p495 p577 p1187 : Prop)
    (h16152 : (¬ p7))
    (h12956 : p7 ∨ (¬ p43) ∨ (¬ p71) ∨ (¬ p481) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1187)) : (¬ p43) ∨ (¬ p71) ∨ (¬ p481) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p43 := by
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
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12956 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17850 (p7 p310 p501 p636 p1061 p1076 : Prop)
    (h16152 : (¬ p7))
    (h12958 : p7 ∨ (¬ p310) ∨ (¬ p501) ∨ (¬ p636) ∨ (¬ p1061) ∨ (¬ p1076)) : (¬ p310) ∨ (¬ p501) ∨ (¬ p636) ∨ (¬ p1061) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p501 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12958 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17851 (p7 p129 p142 p207 p310 p343 p344 p1061 p1076 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h1950 : p343)
    (h12959 : p7 ∨ p129 ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p310) ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p1061) ∨ (¬ p1076)) : (¬ p142) ∨ (¬ p207) ∨ (¬ p310) ∨ (¬ p344) ∨ (¬ p1061) ∨ (¬ p1076) := by
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
  have u2 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p129) := by
    exact h16154
  have u8 : p343 := by
    exact h1950
  rcases h12959 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step17852 (p7 p12 p108 p127 p133 p343 p344 p1076 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h1950 : p343)
    (h12960 : p7 ∨ (¬ p12) ∨ (¬ p108) ∨ (¬ p127) ∨ p133 ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p1076)) : (¬ p12) ∨ (¬ p108) ∨ (¬ p127) ∨ (¬ p344) ∨ (¬ p1076) := by
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
  have u2 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p133) := by
    exact h16157
  have u7 : p343 := by
    exact h1950
  rcases h12960 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step17853 (p7 p189 p239 p344 p545 p796 p1061 p1076 : Prop)
    (h16152 : (¬ p7))
    (h12961 : p7 ∨ (¬ p189) ∨ (¬ p239) ∨ (¬ p344) ∨ (¬ p545) ∨ (¬ p796) ∨ (¬ p1061) ∨ (¬ p1076)) : (¬ p189) ∨ (¬ p239) ∨ (¬ p344) ∨ (¬ p545) ∨ (¬ p796) ∨ (¬ p1061) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p239 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
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
  have u5 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12961 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17854 (p7 p9 p16 p814 p858 p903 p1061 p1074 p1334 p1542 : Prop)
    (h16152 : (¬ p7))
    (h12963 : p7 ∨ (¬ p9) ∨ (¬ p16) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p903) ∨ (¬ p1061) ∨ (¬ p1074) ∨ (¬ p1334) ∨ (¬ p1542)) : (¬ p9) ∨ (¬ p16) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p903) ∨ (¬ p1061) ∨ (¬ p1074) ∨ (¬ p1334) ∨ (¬ p1542) := by
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
  have u2 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p903 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h12963 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17855 (p7 p16 p134 p189 p234 p310 p330 p498 p879 p1061 p1074 : Prop)
    (h16152 : (¬ p7))
    (h12964 : p7 ∨ (¬ p16) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p234) ∨ (¬ p310) ∨ (¬ p330) ∨ (¬ p498) ∨ (¬ p879) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p16) ∨ (¬ p134) ∨ (¬ p189) ∨ (¬ p234) ∨ (¬ p310) ∨ (¬ p330) ∨ (¬ p498) ∨ (¬ p879) ∨ (¬ p1061) ∨ (¬ p1074) := by
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
  have u3 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p879 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h12964 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step17856 (p7 p16 p455 p499 p814 p1015 p1335 p1452 : Prop)
    (h16152 : (¬ p7))
    (h12965 : p7 ∨ (¬ p16) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p814) ∨ (¬ p1015) ∨ (¬ p1335) ∨ (¬ p1452)) : (¬ p16) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p814) ∨ (¬ p1015) ∨ (¬ p1335) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
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
  have u3 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12965 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17857 (p7 p16 p343 p344 p499 p633 p814 p858 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16309 : (¬ p1324))
    (h12966 : p7 ∨ (¬ p16) ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p814) ∨ (¬ p858) ∨ p1324 ∨ (¬ p1325)) : (¬ p16) ∨ (¬ p344) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p858 := by
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
  rcases h12966 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u9 q8)
  · exact False.elim (q9 u6)

theorem step17860 (p7 p15 p19 p323 p387 p1135 p1136 : Prop)
    (h16152 : (¬ p7))
    (h6744 : p1135)
    (h16259 : (¬ p1136))
    (h12969 : p7 ∨ (¬ p15) ∨ (¬ p19) ∨ (¬ p323) ∨ (¬ p387) ∨ (¬ p1135) ∨ p1136) : (¬ p15) ∨ (¬ p19) ∨ (¬ p323) ∨ (¬ p387) := by
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
  have u3 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p1135 := by
    exact h6744
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h12969 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)

theorem step17861 (p7 p10 p102 p499 p601 p1075 p1136 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16259 : (¬ p1136))
    (h12970 : p7 ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1075) ∨ p1136) : (¬ p10) ∨ (¬ p102) ∨ (¬ p499) ∨ (¬ p601) := by
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
  have u2 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p1075 := by
    exact h6478
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h12970 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)

theorem step17862 (p7 p71 p127 p323 p420 p633 p1075 p1136 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16259 : (¬ p1136))
    (h12972 : p7 ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p323) ∨ (¬ p420) ∨ (¬ p633) ∨ (¬ p1075) ∨ p1136) : (¬ p71) ∨ (¬ p127) ∨ (¬ p323) ∨ (¬ p420) ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p1075 := by
    exact h6478
  have u7 : (¬ p1136) := by
    exact h16259
  rcases h12972 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u6)
  · exact False.elim (u7 q7)

theorem step17863 (p7 p19 p102 p133 p481 p1075 p1187 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h6478 : p1075)
    (h12973 : p7 ∨ (¬ p19) ∨ (¬ p102) ∨ p133 ∨ (¬ p481) ∨ (¬ p1075) ∨ (¬ p1187)) : (¬ p19) ∨ (¬ p102) ∨ (¬ p481) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p102 := by
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
  have u5 : (¬ p133) := by
    exact h16157
  have u6 : p1075 := by
    exact h6478
  rcases h12973 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step17864 (p7 p15 p16 p234 p1330 p1349 p1366 p1489 : Prop)
    (h16152 : (¬ p7))
    (h12974 : p7 ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p234) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p1366) ∨ (¬ p1489)) : (¬ p15) ∨ (¬ p16) ∨ (¬ p234) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p1366) ∨ (¬ p1489) := by
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
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h12974 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17865 (p7 p8 p14 p540 p563 p1187 : Prop)
    (h16152 : (¬ p7))
    (h12975 : p7 ∨ (¬ p8) ∨ (¬ p14) ∨ (¬ p540) ∨ (¬ p563) ∨ (¬ p1187)) : (¬ p8) ∨ (¬ p14) ∨ (¬ p540) ∨ (¬ p563) ∨ (¬ p1187) := by
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
  have u2 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p563 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12975 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17866 (p7 p18 p127 p133 p234 p328 p387 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h6744 : p1135)
    (h12976 : p7 ∨ (¬ p18) ∨ (¬ p127) ∨ p133 ∨ (¬ p234) ∨ (¬ p328) ∨ (¬ p387) ∨ (¬ p1135)) : (¬ p18) ∨ (¬ p127) ∨ (¬ p234) ∨ (¬ p328) ∨ (¬ p387) := by
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
  have u3 : p328 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p133) := by
    exact h16157
  have u7 : p1135 := by
    exact h6744
  rcases h12976 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step17867 (p7 p8 p171 p189 p242 p897 p926 : Prop)
    (h16152 : (¬ p7))
    (h12977 : p7 ∨ (¬ p8) ∨ (¬ p171) ∨ (¬ p189) ∨ (¬ p242) ∨ (¬ p897) ∨ (¬ p926)) : (¬ p8) ∨ (¬ p171) ∨ (¬ p189) ∨ (¬ p242) ∨ (¬ p897) ∨ (¬ p926) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12977 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17868 (p7 p18 p127 p172 p185 p187 p234 p539 p790 p802 : Prop)
    (h16152 : (¬ p7))
    (h12978 : p7 ∨ (¬ p18) ∨ (¬ p127) ∨ (¬ p172) ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p234) ∨ (¬ p539) ∨ (¬ p790) ∨ (¬ p802)) : (¬ p18) ∨ (¬ p127) ∨ (¬ p172) ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p234) ∨ (¬ p539) ∨ (¬ p790) ∨ (¬ p802) := by
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
  have u2 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p539 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p802 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h12978 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17869 (p7 p14 p16 p18 p71 p127 p164 p814 p858 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h789 : p164)
    (h16309 : (¬ p1324))
    (h12979 : p7 ∨ (¬ p14) ∨ (¬ p16) ∨ (¬ p18) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p164) ∨ (¬ p814) ∨ (¬ p858) ∨ p1324 ∨ (¬ p1325)) : (¬ p14) ∨ (¬ p16) ∨ (¬ p18) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p127 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p164 := by
    exact h789
  have u10 : (¬ p1324) := by
    exact h16309
  rcases h12979 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step17870 (p7 p15 p16 p19 p102 p814 p858 p1075 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16309 : (¬ p1324))
    (h12980 : p7 ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p19) ∨ (¬ p102) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1075) ∨ p1324 ∨ (¬ p1325)) : (¬ p15) ∨ (¬ p16) ∨ (¬ p19) ∨ (¬ p102) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1325) := by
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
  have u2 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p1075 := by
    exact h6478
  have u9 : (¬ p1324) := by
    exact h16309
  rcases h12980 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u8)
  · exact False.elim (u9 q8)
  · exact False.elim (q9 u6)

theorem step17871 (p7 p925 p980 p1074 p1122 p1508 : Prop)
    (h16152 : (¬ p7))
    (h12981 : p7 ∨ (¬ p925) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1122) ∨ (¬ p1508)) : (¬ p925) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1122) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p925 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1122 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h12981 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17872 (p7 p302 p734 p858 p897 p1022 p1531 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h9335 : p1531)
    (h12982 : p7 ∨ p302 ∨ (¬ p734) ∨ (¬ p858) ∨ (¬ p897) ∨ (¬ p1022) ∨ (¬ p1531)) : (¬ p734) ∨ (¬ p858) ∨ (¬ p897) ∨ (¬ p1022) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p302) := by
    exact h16285
  have u6 : p1531 := by
    exact h9335
  rcases h12982 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17873 (p133 p142 p195 p788 : Prop)
    (h16157 : (¬ p133))
    (h5066 : p788)
    (h12983 : p133 ∨ (¬ p142) ∨ p195 ∨ (¬ p788)) : (¬ p142) ∨ p195 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p195) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p133) := by
    exact h16157
  have u3 : p788 := by
    exact h5066
  rcases h12983 with q0 | q1 | q2 | q3
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)

theorem step17875 (p7 p15 p16 p19 p121 p228 p814 p858 : Prop)
    (h16152 : (¬ p7))
    (h12985 : p7 ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p19) ∨ (¬ p121) ∨ (¬ p228) ∨ (¬ p814) ∨ (¬ p858)) : (¬ p15) ∨ (¬ p16) ∨ (¬ p19) ∨ (¬ p121) ∨ (¬ p228) ∨ (¬ p814) ∨ (¬ p858) := by
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
  have u2 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p228 := by
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
  rcases h12985 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17876 (p7 p21 p72 p127 p387 p431 p435 p601 p1187 : Prop)
    (h16152 : (¬ p7))
    (h12986 : p7 ∨ (¬ p21) ∨ (¬ p72) ∨ (¬ p127) ∨ (¬ p387) ∨ (¬ p431) ∨ (¬ p435) ∨ (¬ p601) ∨ (¬ p1187)) : (¬ p21) ∨ (¬ p72) ∨ (¬ p127) ∨ (¬ p387) ∨ (¬ p431) ∨ (¬ p435) ∨ (¬ p601) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12986 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17877 (p7 p18 p127 p133 p234 p346 p543 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h6478 : p1075)
    (h12987 : p7 ∨ (¬ p18) ∨ (¬ p127) ∨ p133 ∨ (¬ p234) ∨ (¬ p346) ∨ (¬ p543) ∨ (¬ p1075)) : (¬ p18) ∨ (¬ p127) ∨ (¬ p234) ∨ (¬ p346) ∨ (¬ p543) := by
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
  have u3 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p543 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p133) := by
    exact h16157
  have u7 : p1075 := by
    exact h6478
  rcases h12987 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step17878 (p3 p7 p72 p382 p480 p880 p1075 p1076 p1095 p1187 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16309 : (¬ p1324))
    (h12988 : (¬ p3) ∨ p7 ∨ (¬ p72) ∨ (¬ p382) ∨ (¬ p480) ∨ (¬ p880) ∨ (¬ p1075) ∨ (¬ p1076) ∨ (¬ p1095) ∨ (¬ p1187) ∨ p1324 ∨ (¬ p1325)) : (¬ p3) ∨ (¬ p72) ∨ (¬ p382) ∨ (¬ p480) ∨ (¬ p880) ∨ (¬ p1076) ∨ (¬ p1095) ∨ (¬ p1187) ∨ (¬ p1325) := by
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
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p480 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p1075 := by
    exact h6478
  have u11 : (¬ p1324) := by
    exact h16309
  rcases h12988 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u0)
  · exact False.elim (u9 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (u11 q10)
  · exact False.elim (q11 u8)

theorem step17879 (p7 p21 p72 p127 p382 p434 p480 p601 p1187 p1334 : Prop)
    (h16152 : (¬ p7))
    (h12989 : p7 ∨ (¬ p21) ∨ (¬ p72) ∨ (¬ p127) ∨ (¬ p382) ∨ (¬ p434) ∨ (¬ p480) ∨ (¬ p601) ∨ (¬ p1187) ∨ (¬ p1334)) : (¬ p21) ∨ (¬ p72) ∨ (¬ p127) ∨ (¬ p382) ∨ (¬ p434) ∨ (¬ p480) ∨ (¬ p601) ∨ (¬ p1187) ∨ (¬ p1334) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p480 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h12989 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17880 (p3 p7 p72 p302 p858 p880 p1022 p1075 p1076 p1095 p1188 p1545 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h6478 : p1075)
    (h12990 : (¬ p3) ∨ p7 ∨ (¬ p72) ∨ p302 ∨ (¬ p858) ∨ (¬ p880) ∨ (¬ p1022) ∨ (¬ p1075) ∨ (¬ p1076) ∨ (¬ p1095) ∨ (¬ p1188) ∨ (¬ p1545)) : (¬ p3) ∨ (¬ p72) ∨ (¬ p858) ∨ (¬ p880) ∨ (¬ p1022) ∨ (¬ p1076) ∨ (¬ p1095) ∨ (¬ p1188) ∨ (¬ p1545) := by
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
  have u2 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p302) := by
    exact h16285
  have u11 : p1075 := by
    exact h6478
  rcases h12990 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u0)
  · exact False.elim (u9 q1)
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

theorem step17881 (p7 p161 p290 p1076 p1122 p1310 p1508 : Prop)
    (h16152 : (¬ p7))
    (h12991 : p7 ∨ (¬ p161) ∨ (¬ p290) ∨ (¬ p1076) ∨ (¬ p1122) ∨ (¬ p1310) ∨ (¬ p1508)) : (¬ p161) ∨ (¬ p290) ∨ (¬ p1076) ∨ (¬ p1122) ∨ (¬ p1310) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p290 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1122 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12991 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17883 (p7 p10 p18 p72 p211 p362 : Prop)
    (h16152 : (¬ p7))
    (h12993 : p7 ∨ (¬ p10) ∨ (¬ p18) ∨ (¬ p72) ∨ (¬ p211) ∨ (¬ p362)) : (¬ p10) ∨ (¬ p18) ∨ (¬ p72) ∨ (¬ p211) ∨ (¬ p362) := by
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
  have u2 : p72 := by
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
  rcases h12993 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17885 (p3 p7 p133 p142 p167 p323 p427 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h2334 : p427)
    (h12996 : (¬ p3) ∨ p7 ∨ p133 ∨ (¬ p142) ∨ (¬ p167) ∨ (¬ p323) ∨ (¬ p427)) : (¬ p3) ∨ (¬ p142) ∨ (¬ p167) ∨ (¬ p323) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p133) := by
    exact h16157
  have u6 : p427 := by
    exact h2334
  rcases h12996 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17886 (p7 p16 p71 p185 p303 p347 p481 p836 p996 : Prop)
    (h16152 : (¬ p7))
    (h12997 : p7 ∨ (¬ p16) ∨ (¬ p71) ∨ (¬ p185) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p481) ∨ (¬ p836) ∨ (¬ p996)) : (¬ p16) ∨ (¬ p71) ∨ (¬ p185) ∨ (¬ p303) ∨ (¬ p347) ∨ (¬ p481) ∨ (¬ p836) ∨ (¬ p996) := by
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
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p481 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h12997 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step17887 (p7 p14 p16 p18 p71 p127 p172 p238 p710 p840 : Prop)
    (h16152 : (¬ p7))
    (h12998 : p7 ∨ (¬ p14) ∨ (¬ p16) ∨ (¬ p18) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p172) ∨ (¬ p238) ∨ (¬ p710) ∨ (¬ p840)) : (¬ p14) ∨ (¬ p16) ∨ (¬ p18) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p172) ∨ (¬ p238) ∨ (¬ p710) ∨ (¬ p840) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h12998 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17888 (p7 p46 p170 p229 p560 p710 p840 : Prop)
    (h16152 : (¬ p7))
    (h12999 : p7 ∨ (¬ p46) ∨ (¬ p170) ∨ (¬ p229) ∨ (¬ p560) ∨ (¬ p710) ∨ (¬ p840)) : (¬ p46) ∨ (¬ p170) ∨ (¬ p229) ∨ (¬ p560) ∨ (¬ p710) ∨ (¬ p840) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p46 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p170 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h12999 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17889 (p3 p6 p7 p107 p1080 p1206 : Prop)
    (h16152 : (¬ p7))
    (h13000 : (¬ p3) ∨ (¬ p6) ∨ p7 ∨ (¬ p107) ∨ (¬ p1080) ∨ (¬ p1206)) : (¬ p3) ∨ (¬ p6) ∨ (¬ p107) ∨ (¬ p1080) ∨ (¬ p1206) := by
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
  have u3 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13000 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17890 (p7 p41 p87 p185 p187 p481 p669 p926 p996 p1074 : Prop)
    (h16152 : (¬ p7))
    (h13001 : p7 ∨ (¬ p41) ∨ (¬ p87) ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p481) ∨ (¬ p669) ∨ (¬ p926) ∨ (¬ p996) ∨ (¬ p1074)) : (¬ p41) ∨ (¬ p87) ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p481) ∨ (¬ p669) ∨ (¬ p926) ∨ (¬ p996) ∨ (¬ p1074) := by
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
  have u5 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h13001 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step17891 (p7 p303 p420 p426 p633 p657 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h6478 : p1075)
    (h13003 : p7 ∨ (¬ p303) ∨ (¬ p420) ∨ p426 ∨ (¬ p633) ∨ (¬ p657) ∨ (¬ p1075)) : (¬ p303) ∨ (¬ p420) ∨ (¬ p633) ∨ (¬ p657) := by
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
  have u2 : p633 := by
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
  have u6 : p1075 := by
    exact h6478
  rcases h13003 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17892 (p7 p70 p85 p481 p669 p918 p996 p1115 : Prop)
    (h16152 : (¬ p7))
    (h13004 : p7 ∨ (¬ p70) ∨ (¬ p85) ∨ (¬ p481) ∨ (¬ p669) ∨ (¬ p918) ∨ (¬ p996) ∨ (¬ p1115)) : (¬ p70) ∨ (¬ p85) ∨ (¬ p481) ∨ (¬ p669) ∨ (¬ p918) ∨ (¬ p996) ∨ (¬ p1115) := by
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
  have u3 : p669 := by
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
  have u6 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13004 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17893 (p7 p10 p102 p303 p426 p657 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h6478 : p1075)
    (h13005 : p7 ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p303) ∨ p426 ∨ (¬ p657) ∨ (¬ p1075)) : (¬ p10) ∨ (¬ p102) ∨ (¬ p303) ∨ (¬ p657) := by
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
  have u2 : p303 := by
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
  have u6 : p1075 := by
    exact h6478
  rcases h13005 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17894 (p7 p10 p27 p495 p595 p596 : Prop)
    (h16152 : (¬ p7))
    (h13006 : p7 ∨ (¬ p10) ∨ (¬ p27) ∨ (¬ p495) ∨ (¬ p595) ∨ (¬ p596)) : (¬ p10) ∨ (¬ p27) ∨ (¬ p495) ∨ (¬ p595) ∨ (¬ p596) := by
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
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p596 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13006 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17895 (p7 p24 p40 p69 p323 p387 p499 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h6744 : p1135)
    (h13007 : p7 ∨ (¬ p24) ∨ p40 ∨ (¬ p69) ∨ (¬ p323) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p1135)) : (¬ p24) ∨ (¬ p69) ∨ (¬ p323) ∨ (¬ p387) ∨ (¬ p499) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p40) := by
    exact h16150
  have u7 : p1135 := by
    exact h6744
  rcases h13007 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step17896 (p3 p7 p133 p346 p544 p1077 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h6761 : p1139)
    (h13008 : (¬ p3) ∨ p7 ∨ p133 ∨ (¬ p346) ∨ (¬ p544) ∨ (¬ p1077) ∨ (¬ p1139)) : (¬ p3) ∨ (¬ p346) ∨ (¬ p544) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p133) := by
    exact h16157
  have u6 : p1139 := by
    exact h6761
  rcases h13008 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17897 (p7 p46 p189 p790 p801 p1187 : Prop)
    (h16152 : (¬ p7))
    (h13009 : p7 ∨ (¬ p46) ∨ (¬ p189) ∨ (¬ p790) ∨ (¬ p801) ∨ (¬ p1187)) : (¬ p46) ∨ (¬ p189) ∨ (¬ p790) ∨ (¬ p801) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p46 := by
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
  have u4 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13009 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17898 (p533 p983 p1181 p1603 : Prop)
    (h16272 : (¬ p1181))
    (h9837 : p1603)
    (h13011 : p533 ∨ (¬ p983) ∨ p1181 ∨ (¬ p1603)) : p533 ∨ (¬ p983) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p533) := fun hu => hn (Or.inl hu)
  have u1 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p1181) := by
    exact h16272
  have u3 : p1603 := by
    exact h9837
  rcases h13011 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)

theorem step17899 (p7 p185 p727 p790 p833 p1584 : Prop)
    (h16152 : (¬ p7))
    (h13012 : p7 ∨ (¬ p185) ∨ (¬ p727) ∨ (¬ p790) ∨ (¬ p833) ∨ (¬ p1584)) : (¬ p185) ∨ (¬ p727) ∨ (¬ p790) ∨ (¬ p833) ∨ (¬ p1584) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p727 := by
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
  have u4 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13012 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17900 (p7 p162 p229 p233 p234 p537 p940 : Prop)
    (h16152 : (¬ p7))
    (h16160 : (¬ p162))
    (h2345 : p233)
    (h13013 : p7 ∨ p162 ∨ (¬ p229) ∨ (¬ p233) ∨ (¬ p234) ∨ (¬ p537) ∨ (¬ p940)) : (¬ p229) ∨ (¬ p234) ∨ (¬ p537) ∨ (¬ p940) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p162) := by
    exact h16160
  have u6 : p233 := by
    exact h2345
  rcases h13013 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step17901 (p7 p382 p499 p533 p621 p633 p756 p1325 : Prop)
    (h16152 : (¬ p7))
    (h13014 : p7 ∨ (¬ p382) ∨ (¬ p499) ∨ (¬ p533) ∨ (¬ p621) ∨ (¬ p633) ∨ (¬ p756) ∨ (¬ p1325)) : (¬ p382) ∨ (¬ p499) ∨ (¬ p533) ∨ (¬ p621) ∨ (¬ p633) ∨ (¬ p756) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p382 := by
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
  have u3 : p621 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h13014 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step17902 (p7 p17 p160 p520 p856 p1353 p1489 : Prop)
    (h16152 : (¬ p7))
    (h13015 : p7 ∨ (¬ p17) ∨ (¬ p160) ∨ (¬ p520) ∨ (¬ p856) ∨ (¬ p1353) ∨ (¬ p1489)) : (¬ p17) ∨ (¬ p160) ∨ (¬ p520) ∨ (¬ p856) ∨ (¬ p1353) ∨ (¬ p1489) := by
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
  have u2 : p520 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p856 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1353 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13015 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17904 (p7 p499 p633 p983 p1077 p1136 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16259 : (¬ p1136))
    (h8348 : p1386)
    (h13019 : p7 ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p983) ∨ (¬ p1077) ∨ p1136 ∨ (¬ p1386)) : (¬ p499) ∨ (¬ p633) ∨ (¬ p983) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p1136) := by
    exact h16259
  have u6 : p1386 := by
    exact h8348
  rcases h13019 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step17905 (p7 p455 p499 p980 p1136 p1139 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16259 : (¬ p1136))
    (h6761 : p1139)
    (h13020 : p7 ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p980) ∨ p1136 ∨ (¬ p1139) ∨ (¬ p1452)) : (¬ p455) ∨ (¬ p499) ∨ (¬ p980) ∨ (¬ p1452) := by
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
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p1136) := by
    exact h16259
  have u6 : p1139 := by
    exact h6761
  rcases h13020 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step17906 (p23 p127 p133 p1530 : Prop)
    (h16157 : (¬ p133))
    (h9352 : p1530)
    (h13021 : p23 ∨ (¬ p127) ∨ p133 ∨ (¬ p1530)) : p23 ∨ (¬ p127) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p23) := fun hu => hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p133) := by
    exact h16157
  have u3 : p1530 := by
    exact h9352
  rcases h13021 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)

theorem step17907 (p7 p18 p125 p209 p234 p328 : Prop)
    (h16152 : (¬ p7))
    (h13023 : p7 ∨ (¬ p18) ∨ (¬ p125) ∨ (¬ p209) ∨ (¬ p234) ∨ (¬ p328)) : (¬ p18) ∨ (¬ p125) ∨ (¬ p209) ∨ (¬ p234) ∨ (¬ p328) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p209 := by
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
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13023 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17908 (p7 p10 p102 p362 p658 p1077 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16199 : (¬ p658))
    (h6761 : p1139)
    (h13024 : p7 ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p362) ∨ p658 ∨ (¬ p1077) ∨ (¬ p1139)) : (¬ p10) ∨ (¬ p102) ∨ (¬ p362) ∨ (¬ p1077) := by
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
  have u2 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p658) := by
    exact h16199
  have u6 : p1139 := by
    exact h6761
  rcases h13024 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step17909 (p7 p224 p343 p387 p499 p601 p1136 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16259 : (¬ p1136))
    (h13025 : p7 ∨ (¬ p224) ∨ (¬ p343) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ p1136) : (¬ p224) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p387 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p343 := by
    exact h1950
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h13025 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step17910 (p122 p209 p227 p257 : Prop)
    (h10260 : p122)
    (h16170 : (¬ p257))
    (h13026 : (¬ p122) ∨ p209 ∨ (¬ p227) ∨ p257) : p209 ∨ (¬ p227) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p209) := fun hu => hn (Or.inl hu)
  have u1 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p122 := by
    exact h10260
  have u3 : (¬ p257) := by
    exact h16170
  rcases h13026 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u3 q3)

theorem step17911 (p7 p227 p228 p266 p814 p858 : Prop)
    (h16152 : (¬ p7))
    (h13027 : p7 ∨ (¬ p227) ∨ (¬ p228) ∨ (¬ p266) ∨ (¬ p814) ∨ (¬ p858)) : (¬ p227) ∨ (¬ p228) ∨ (¬ p266) ∨ (¬ p814) ∨ (¬ p858) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p266 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13027 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17912 (p7 p125 p224 p227 p351 p383 : Prop)
    (h16152 : (¬ p7))
    (h13029 : p7 ∨ (¬ p125) ∨ (¬ p224) ∨ (¬ p227) ∨ (¬ p351) ∨ (¬ p383)) : (¬ p125) ∨ (¬ p224) ∨ (¬ p227) ∨ (¬ p351) ∨ (¬ p383) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p383 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13029 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17913 (p3 p6 p7 p12 p257 p1075 p1076 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h6478 : p1075)
    (h13030 : (¬ p3) ∨ (¬ p6) ∨ p7 ∨ (¬ p12) ∨ p257 ∨ (¬ p1075) ∨ (¬ p1076)) : (¬ p3) ∨ (¬ p6) ∨ (¬ p12) ∨ (¬ p1076) := by
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
  have u2 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p257) := by
    exact h16170
  have u6 : p1075 := by
    exact h6478
  rcases h13030 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u4 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step17914 (p191 p193 p659 p791 : Prop)
    (h3753 : p659)
    (h16213 : (¬ p791))
    (h13031 : p191 ∨ (¬ p193) ∨ (¬ p659) ∨ p791) : p191 ∨ (¬ p193) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p191) := fun hu => hn (Or.inl hu)
  have u1 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p659 := by
    exact h3753
  have u3 : (¬ p791) := by
    exact h16213
  rcases h13031 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)

theorem step17915 (p7 p290 p303 p345 p657 p840 : Prop)
    (h16152 : (¬ p7))
    (h13033 : p7 ∨ (¬ p290) ∨ (¬ p303) ∨ (¬ p345) ∨ (¬ p657) ∨ (¬ p840)) : (¬ p290) ∨ (¬ p303) ∨ (¬ p345) ∨ (¬ p657) ∨ (¬ p840) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p290 := by
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
  have u3 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13033 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17917 (p7 p127 p326 p382 p477 p996 : Prop)
    (h16152 : (¬ p7))
    (h13035 : p7 ∨ (¬ p127) ∨ (¬ p326) ∨ (¬ p382) ∨ (¬ p477) ∨ (¬ p996)) : (¬ p127) ∨ (¬ p326) ∨ (¬ p382) ∨ (¬ p477) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p477 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13035 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17918 (p1 p7 p105 p127 p382 p477 p996 : Prop)
    (h16152 : (¬ p7))
    (h13038 : (¬ p1) ∨ p7 ∨ (¬ p105) ∨ (¬ p127) ∨ (¬ p382) ∨ (¬ p477) ∨ (¬ p996)) : (¬ p1) ∨ (¬ p105) ∨ (¬ p127) ∨ (¬ p382) ∨ (¬ p477) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p477 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13038 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step17920 (p7 p17 p41 p138 p1249 p1346 : Prop)
    (h16152 : (¬ p7))
    (h13040 : p7 ∨ (¬ p17) ∨ (¬ p41) ∨ (¬ p138) ∨ (¬ p1249) ∨ (¬ p1346)) : (¬ p17) ∨ (¬ p41) ∨ (¬ p138) ∨ (¬ p1249) ∨ (¬ p1346) := by
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
  have u2 : p138 := by
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
  rcases h13040 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17921 (p7 p790 p800 p857 p996 p1349 : Prop)
    (h16152 : (¬ p7))
    (h13041 : p7 ∨ (¬ p790) ∨ (¬ p800) ∨ (¬ p857) ∨ (¬ p996) ∨ (¬ p1349)) : (¬ p790) ∨ (¬ p800) ∨ (¬ p857) ∨ (¬ p996) ∨ (¬ p1349) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p800 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p857 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13041 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17922 (p7 p191 p382 p424 p477 p996 : Prop)
    (h16152 : (¬ p7))
    (h13042 : p7 ∨ (¬ p191) ∨ (¬ p382) ∨ (¬ p424) ∨ (¬ p477) ∨ (¬ p996)) : (¬ p191) ∨ (¬ p382) ∨ (¬ p424) ∨ (¬ p477) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p477 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13042 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17923 (p7 p17 p109 p137 p163 p193 : Prop)
    (h16152 : (¬ p7))
    (h13043 : p7 ∨ (¬ p17) ∨ (¬ p109) ∨ (¬ p137) ∨ (¬ p163) ∨ (¬ p193)) : (¬ p17) ∨ (¬ p109) ∨ (¬ p137) ∨ (¬ p163) ∨ (¬ p193) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p137 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h13043 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step17924 (p7 p101 p329 p350 p367 p382 p996 : Prop)
    (h16152 : (¬ p7))
    (h13044 : p7 ∨ (¬ p101) ∨ (¬ p329) ∨ (¬ p350) ∨ (¬ p367) ∨ (¬ p382) ∨ (¬ p996)) : (¬ p101) ∨ (¬ p329) ∨ (¬ p350) ∨ (¬ p367) ∨ (¬ p382) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p329 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p367 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h13044 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

#print axioms step17924

end NineRUPTrial
