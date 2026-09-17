import Mathlib.Tactic.Tauto

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineRUPTrial

theorem step19106 (p7 p39 p68 p301 p302 p303 p343 p544 p561 p576 p1036 p1061 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h1950 : p343)
    (h14465 : p7 ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p301) ∨ p302 ∨ (¬ p303) ∨ (¬ p343) ∨ (¬ p544) ∨ (¬ p561) ∨ (¬ p576) ∨ (¬ p1036) ∨ (¬ p1061)) : (¬ p39) ∨ (¬ p68) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p544) ∨ (¬ p561) ∨ (¬ p576) ∨ (¬ p1036) ∨ (¬ p1061) := by
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
  have u2 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
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
  have u6 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p302) := by
    exact h16285
  have u11 : p343 := by
    exact h1950
  rcases h14465 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
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

theorem step19107 (p7 p38 p129 p163 p226 p261 p279 p423 p532 p961 p1000 p1333 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h1444 : p279)
    (h14466 : p7 ∨ (¬ p38) ∨ p129 ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p261) ∨ (¬ p279) ∨ (¬ p423) ∨ (¬ p532) ∨ (¬ p961) ∨ (¬ p1000) ∨ (¬ p1333)) : (¬ p38) ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p261) ∨ (¬ p423) ∨ (¬ p532) ∨ (¬ p961) ∨ (¬ p1000) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
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
  have u3 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p129) := by
    exact h16154
  have u11 : p279 := by
    exact h1444
  rcases h14466 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
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

theorem step19108 (p7 p43 p135 p163 p229 p581 : Prop)
    (h16152 : (¬ p7))
    (h14468 : p7 ∨ (¬ p43) ∨ (¬ p135) ∨ (¬ p163) ∨ (¬ p229) ∨ (¬ p581)) : (¬ p43) ∨ (¬ p135) ∨ (¬ p163) ∨ (¬ p229) ∨ (¬ p581) := by
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
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14468 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19109 (p7 p63 p69 p129 p163 p229 p792 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h4535 : p792)
    (h14469 : p7 ∨ (¬ p63) ∨ (¬ p69) ∨ p129 ∨ (¬ p163) ∨ (¬ p229) ∨ (¬ p792)) : (¬ p63) ∨ (¬ p69) ∨ (¬ p163) ∨ (¬ p229) := by
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
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p792 := by
    exact h4535
  rcases h14469 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19110 (p3 p7 p19 p71 p125 p126 p143 p229 p500 : Prop)
    (h16152 : (¬ p7))
    (h14470 : (¬ p3) ∨ p7 ∨ (¬ p19) ∨ (¬ p71) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p143) ∨ (¬ p229) ∨ (¬ p500)) : (¬ p3) ∨ (¬ p19) ∨ (¬ p71) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p143) ∨ (¬ p229) ∨ (¬ p500) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
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
  have u3 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14470 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19111 (p3 p7 p18 p72 p125 p210 p303 p665 p880 p1095 : Prop)
    (h16152 : (¬ p7))
    (h14471 : (¬ p3) ∨ p7 ∨ (¬ p18) ∨ (¬ p72) ∨ (¬ p125) ∨ (¬ p210) ∨ (¬ p303) ∨ (¬ p665) ∨ (¬ p880) ∨ (¬ p1095)) : (¬ p3) ∨ (¬ p18) ∨ (¬ p72) ∨ (¬ p125) ∨ (¬ p210) ∨ (¬ p303) ∨ (¬ p665) ∨ (¬ p880) ∨ (¬ p1095) := by
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
  have u3 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p665 := by
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
  rcases h14471 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19112 (p3 p7 p18 p72 p210 p351 p363 p382 p387 p880 p904 : Prop)
    (h16152 : (¬ p7))
    (h14472 : (¬ p3) ∨ p7 ∨ (¬ p18) ∨ (¬ p72) ∨ (¬ p210) ∨ (¬ p351) ∨ (¬ p363) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p880) ∨ (¬ p904)) : (¬ p3) ∨ (¬ p18) ∨ (¬ p72) ∨ (¬ p210) ∨ (¬ p351) ∨ (¬ p363) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p880) ∨ (¬ p904) := by
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
  have u4 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p363 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h14472 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19113 (p3 p7 p16 p17 p19 p71 p229 p301 p302 p303 p788 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h5066 : p788)
    (h14473 : (¬ p3) ∨ p7 ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p19) ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p301) ∨ p302 ∨ (¬ p303) ∨ (¬ p788)) : (¬ p3) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p19) ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p301) ∨ (¬ p303) := by
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
  have u3 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p302) := by
    exact h16285
  have u10 : p788 := by
    exact h5066
  rcases h14473 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19114 (p3 p7 p71 p229 p423 p1035 p1136 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16259 : (¬ p1136))
    (h8348 : p1386)
    (h14474 : (¬ p3) ∨ p7 ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p423) ∨ (¬ p1035) ∨ p1136 ∨ (¬ p1386)) : (¬ p3) ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p423) ∨ (¬ p1035) := by
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
  have u3 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p1136) := by
    exact h16259
  have u7 : p1386 := by
    exact h8348
  rcases h14474 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u7)

theorem step19117 (p3 p7 p12 p71 p343 p904 p1074 p1136 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16259 : (¬ p1136))
    (h14477 : (¬ p3) ∨ p7 ∨ (¬ p12) ∨ (¬ p71) ∨ (¬ p343) ∨ (¬ p904) ∨ (¬ p1074) ∨ p1136) : (¬ p3) ∨ (¬ p12) ∨ (¬ p71) ∨ (¬ p904) ∨ (¬ p1074) := by
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
  have u2 : p71 := by
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
  have u6 : p343 := by
    exact h1950
  have u7 : (¬ p1136) := by
    exact h16259
  rcases h14477 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step19118 (p7 p125 p303 p500 p665 p980 p1096 p1225 p1311 : Prop)
    (h16152 : (¬ p7))
    (h14478 : p7 ∨ (¬ p125) ∨ (¬ p303) ∨ (¬ p500) ∨ (¬ p665) ∨ (¬ p980) ∨ (¬ p1096) ∨ (¬ p1225) ∨ (¬ p1311)) : (¬ p125) ∨ (¬ p303) ∨ (¬ p500) ∨ (¬ p665) ∨ (¬ p980) ∨ (¬ p1096) ∨ (¬ p1225) ∨ (¬ p1311) := by
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
  have u2 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1311 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14478 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19119 (p7 p16 p19 p71 p125 p126 p143 p261 p1140 p1141 : Prop)
    (h16152 : (¬ p7))
    (h14479 : p7 ∨ (¬ p16) ∨ (¬ p19) ∨ (¬ p71) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p143) ∨ (¬ p261) ∨ (¬ p1140) ∨ (¬ p1141)) : (¬ p16) ∨ (¬ p19) ∨ (¬ p71) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p143) ∨ (¬ p261) ∨ (¬ p1140) ∨ (¬ p1141) := by
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
  have u3 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p261 := by
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
  rcases h14479 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19120 (p7 p256 p302 p576 p792 p814 p858 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h4535 : p792)
    (h14480 : p7 ∨ (¬ p256) ∨ p302 ∨ (¬ p576) ∨ (¬ p792) ∨ (¬ p814) ∨ (¬ p858)) : (¬ p256) ∨ (¬ p576) ∨ (¬ p814) ∨ (¬ p858) := by
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
  have u3 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p302) := by
    exact h16285
  have u6 : p792 := by
    exact h4535
  rcases h14480 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19121 (p7 p125 p162 p185 p265 p303 p576 p790 p792 p1022 p1334 : Prop)
    (h16152 : (¬ p7))
    (h16160 : (¬ p162))
    (h4535 : p792)
    (h14481 : p7 ∨ (¬ p125) ∨ p162 ∨ (¬ p185) ∨ (¬ p265) ∨ (¬ p303) ∨ (¬ p576) ∨ (¬ p790) ∨ (¬ p792) ∨ (¬ p1022) ∨ (¬ p1334)) : (¬ p125) ∨ (¬ p185) ∨ (¬ p265) ∨ (¬ p303) ∨ (¬ p576) ∨ (¬ p790) ∨ (¬ p1022) ∨ (¬ p1334) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p162) := by
    exact h16160
  have u10 : p792 := by
    exact h4535
  rcases h14481 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19122 (p7 p19 p280 p382 p387 p480 p788 p1187 : Prop)
    (h16152 : (¬ p7))
    (h16173 : (¬ p280))
    (h5066 : p788)
    (h14482 : p7 ∨ (¬ p19) ∨ p280 ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p480) ∨ (¬ p788) ∨ (¬ p1187)) : (¬ p19) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p480) ∨ (¬ p1187) := by
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
  have u2 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p480 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p280) := by
    exact h16173
  have u7 : p788 := by
    exact h5066
  rcases h14482 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step19123 (p3 p7 p71 p229 p234 p327 p382 p387 p621 : Prop)
    (h16152 : (¬ p7))
    (h14483 : (¬ p3) ∨ p7 ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p234) ∨ (¬ p327) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p621)) : (¬ p3) ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p234) ∨ (¬ p327) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p621) := by
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
  have u4 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p621 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14483 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19124 (p3 p7 p125 p133 p229 p265 p303 p423 p576 p792 p1000 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h4535 : p792)
    (h14484 : (¬ p3) ∨ p7 ∨ (¬ p125) ∨ p133 ∨ (¬ p229) ∨ (¬ p265) ∨ (¬ p303) ∨ (¬ p423) ∨ (¬ p576) ∨ (¬ p792) ∨ (¬ p1000)) : (¬ p3) ∨ (¬ p125) ∨ (¬ p229) ∨ (¬ p265) ∨ (¬ p303) ∨ (¬ p423) ∨ (¬ p576) ∨ (¬ p1000) := by
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
  have u2 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p576 := by
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
  rcases h14484 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u9 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u10)
  · exact False.elim (q10 u7)

theorem step19125 (p7 p19 p302 p788 p1141 p1333 p1465 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h5066 : p788)
    (h14485 : p7 ∨ (¬ p19) ∨ p302 ∨ (¬ p788) ∨ (¬ p1141) ∨ (¬ p1333) ∨ (¬ p1465)) : (¬ p19) ∨ (¬ p1141) ∨ (¬ p1333) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1141 := by
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
  have u5 : (¬ p302) := by
    exact h16285
  have u6 : p788 := by
    exact h5066
  rcases h14485 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19126 (p7 p125 p265 p303 p576 p792 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16309 : (¬ p1324))
    (h14486 : p7 ∨ (¬ p125) ∨ (¬ p265) ∨ (¬ p303) ∨ (¬ p576) ∨ (¬ p792) ∨ p1324 ∨ (¬ p1325)) : (¬ p125) ∨ (¬ p265) ∨ (¬ p303) ∨ (¬ p576) ∨ (¬ p1325) := by
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
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p792 := by
    exact h4535
  have u7 : (¬ p1324) := by
    exact h16309
  rcases h14486 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step19127 (p7 p11 p13 p125 p126 p500 p1095 p1096 : Prop)
    (h16152 : (¬ p7))
    (h14487 : p7 ∨ (¬ p11) ∨ (¬ p13) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p500) ∨ (¬ p1095) ∨ (¬ p1096)) : (¬ p11) ∨ (¬ p13) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p500) ∨ (¬ p1095) ∨ (¬ p1096) := by
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
  have u2 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p500 := by
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
  rcases h14487 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19128 (p7 p18 p127 p128 p129 p163 p226 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16154 : (¬ p129))
    (h14488 : p7 ∨ (¬ p18) ∨ (¬ p127) ∨ (¬ p128) ∨ p129 ∨ (¬ p163) ∨ (¬ p226)) : (¬ p18) ∨ (¬ p127) ∨ (¬ p163) ∨ (¬ p226) := by
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
  have u2 : p163 := by
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
  have u6 : (¬ p129) := by
    exact h16154
  rcases h14488 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19129 (p2 p7 p16 p188 p351 p387 p419 p904 p1096 : Prop)
    (h16152 : (¬ p7))
    (h14489 : (¬ p2) ∨ p7 ∨ (¬ p16) ∨ (¬ p188) ∨ (¬ p351) ∨ (¬ p387) ∨ (¬ p419) ∨ (¬ p904) ∨ (¬ p1096)) : (¬ p2) ∨ (¬ p16) ∨ (¬ p188) ∨ (¬ p351) ∨ (¬ p387) ∨ (¬ p419) ∨ (¬ p904) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p351 := by
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
  have u6 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14489 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19130 (p7 p129 p163 p226 p1035 p1140 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h8348 : p1386)
    (h14490 : p7 ∨ p129 ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p1035) ∨ (¬ p1140) ∨ (¬ p1386)) : (¬ p163) ∨ (¬ p226) ∨ (¬ p1035) ∨ (¬ p1140) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p226 := by
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
  rcases h14490 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19131 (p7 p15 p234 p301 p327 p500 p961 p1443 : Prop)
    (h16152 : (¬ p7))
    (h14491 : p7 ∨ (¬ p15) ∨ (¬ p234) ∨ (¬ p301) ∨ (¬ p327) ∨ (¬ p500) ∨ (¬ p961) ∨ (¬ p1443)) : (¬ p15) ∨ (¬ p234) ∨ (¬ p301) ∨ (¬ p327) ∨ (¬ p500) ∨ (¬ p961) ∨ (¬ p1443) := by
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
  have u2 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14491 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19132 (p7 p11 p16 p17 p532 p533 p1096 p1562 : Prop)
    (h16152 : (¬ p7))
    (h14492 : p7 ∨ (¬ p11) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p532) ∨ (¬ p533) ∨ (¬ p1096) ∨ (¬ p1562)) : (¬ p11) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p532) ∨ (¬ p533) ∨ (¬ p1096) ∨ (¬ p1562) := by
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
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p533 := by
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
  rcases h14492 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19133 (p7 p129 p163 p343 p557 p904 p1061 p1074 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h1950 : p343)
    (h14493 : p7 ∨ p129 ∨ (¬ p163) ∨ (¬ p343) ∨ (¬ p557) ∨ (¬ p904) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p163) ∨ (¬ p557) ∨ (¬ p904) ∨ (¬ p1061) ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p904 := by
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
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p343 := by
    exact h1950
  rcases h14493 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step19134 (p7 p16 p17 p301 p303 p665 p1095 p1096 : Prop)
    (h16152 : (¬ p7))
    (h14494 : p7 ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p665) ∨ (¬ p1095) ∨ (¬ p1096)) : (¬ p16) ∨ (¬ p17) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p665) ∨ (¬ p1095) ∨ (¬ p1096) := by
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
  have u2 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p665 := by
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
  rcases h14494 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19135 (p2 p7 p19 p38 p126 p143 p325 : Prop)
    (h16152 : (¬ p7))
    (h14495 : (¬ p2) ∨ p7 ∨ (¬ p19) ∨ (¬ p38) ∨ (¬ p126) ∨ (¬ p143) ∨ (¬ p325)) : (¬ p2) ∨ (¬ p19) ∨ (¬ p38) ∨ (¬ p126) ∨ (¬ p143) ∨ (¬ p325) := by
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
  have u2 : p38 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14495 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19136 (p7 p233 p258 p481 p686 p1159 p1208 p1443 : Prop)
    (h16152 : (¬ p7))
    (h2345 : p233)
    (h16205 : (¬ p686))
    (h14496 : p7 ∨ (¬ p233) ∨ (¬ p258) ∨ (¬ p481) ∨ p686 ∨ (¬ p1159) ∨ (¬ p1208) ∨ (¬ p1443)) : (¬ p258) ∨ (¬ p481) ∨ (¬ p1159) ∨ (¬ p1208) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p481 := by
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
  have u6 : p233 := by
    exact h2345
  have u7 : (¬ p686) := by
    exact h16205
  rcases h14496 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step19138 (p7 p19 p129 p163 p226 p788 p1140 p1141 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h5066 : p788)
    (h14498 : p7 ∨ (¬ p19) ∨ p129 ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p788) ∨ (¬ p1140) ∨ (¬ p1141)) : (¬ p19) ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p1140) ∨ (¬ p1141) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
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
  have u3 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p788 := by
    exact h5066
  rcases h14498 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step19139 (p7 p125 p303 p500 p533 p1096 p1325 p1562 : Prop)
    (h16152 : (¬ p7))
    (h14500 : p7 ∨ (¬ p125) ∨ (¬ p303) ∨ (¬ p500) ∨ (¬ p533) ∨ (¬ p1096) ∨ (¬ p1325) ∨ (¬ p1562)) : (¬ p125) ∨ (¬ p303) ∨ (¬ p500) ∨ (¬ p533) ∨ (¬ p1096) ∨ (¬ p1325) ∨ (¬ p1562) := by
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
  have u2 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14500 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19140 (p7 p39 p69 p88 p351 p382 p387 p815 p904 p1096 : Prop)
    (h16152 : (¬ p7))
    (h14501 : p7 ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p351) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p815) ∨ (¬ p904) ∨ (¬ p1096)) : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p351) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p815) ∨ (¬ p904) ∨ (¬ p1096) := by
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
  have u3 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p815 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14501 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19141 (p7 p14 p15 p351 p382 p387 p544 p621 : Prop)
    (h16152 : (¬ p7))
    (h14502 : p7 ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p351) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p544) ∨ (¬ p621)) : (¬ p14) ∨ (¬ p15) ∨ (¬ p351) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p544) ∨ (¬ p621) := by
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
  have u2 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p621 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14502 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19142 (p7 p63 p769 p924 p1097 p1562 : Prop)
    (h16152 : (¬ p7))
    (h14503 : p7 ∨ (¬ p63) ∨ (¬ p769) ∨ (¬ p924) ∨ (¬ p1097) ∨ (¬ p1562)) : (¬ p63) ∨ (¬ p769) ∨ (¬ p924) ∨ (¬ p1097) ∨ (¬ p1562) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1097 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14503 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19143 (p3 p7 p39 p68 p88 p261 p301 p351 p544 p961 p1443 : Prop)
    (h16152 : (¬ p7))
    (h14504 : (¬ p3) ∨ p7 ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p261) ∨ (¬ p301) ∨ (¬ p351) ∨ (¬ p544) ∨ (¬ p961) ∨ (¬ p1443)) : (¬ p3) ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p261) ∨ (¬ p301) ∨ (¬ p351) ∨ (¬ p544) ∨ (¬ p961) ∨ (¬ p1443) := by
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
  have u5 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h14504 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19144 (p7 p11 p39 p69 p88 p261 p1035 p1145 p1229 p1386 p1445 p1624 p1651 : Prop)
    (h16152 : (¬ p7))
    (h8348 : p1386)
    (h16350 : (¬ p1445))
    (h14506 : p7 ∨ (¬ p11) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p261) ∨ (¬ p1035) ∨ (¬ p1145) ∨ (¬ p1229) ∨ (¬ p1386) ∨ p1445 ∨ (¬ p1624) ∨ (¬ p1651)) : (¬ p11) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p261) ∨ (¬ p1035) ∨ (¬ p1145) ∨ (¬ p1229) ∨ (¬ p1624) ∨ (¬ p1651) := by
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
  have u2 : p69 := by
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
  have u5 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1145 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1651 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : p1386 := by
    exact h8348
  have u12 : (¬ p1445) := by
    exact h16350
  rcases h14506 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u11)
  · exact False.elim (u12 q10)
  · exact False.elim (q11 u8)
  · exact False.elim (q12 u9)

theorem step19145 (p7 p17 p39 p69 p88 p1035 p1145 p1229 p1454 p1644 : Prop)
    (h16152 : (¬ p7))
    (h14507 : p7 ∨ (¬ p17) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p1035) ∨ (¬ p1145) ∨ (¬ p1229) ∨ (¬ p1454) ∨ (¬ p1644)) : (¬ p17) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p1035) ∨ (¬ p1145) ∨ (¬ p1229) ∨ (¬ p1454) ∨ (¬ p1644) := by
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
  have u4 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1145 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1454 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14507 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19146 (p7 p14 p39 p63 p351 p382 p387 p544 p614 : Prop)
    (h16152 : (¬ p7))
    (h14508 : p7 ∨ (¬ p14) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p351) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p544) ∨ (¬ p614)) : (¬ p14) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p351) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p544) ∨ (¬ p614) := by
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
  have u3 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p614 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14508 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19147 (p7 p327 p387 p997 p1333 p1465 : Prop)
    (h16152 : (¬ p7))
    (h14509 : p7 ∨ (¬ p327) ∨ (¬ p387) ∨ (¬ p997) ∨ (¬ p1333) ∨ (¬ p1465)) : (¬ p327) ∨ (¬ p387) ∨ (¬ p997) ∨ (¬ p1333) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p387 := by
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
  rcases h14509 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19149 (p7 p239 p343 p536 p544 p814 p858 p940 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16309 : (¬ p1324))
    (h14512 : p7 ∨ (¬ p239) ∨ (¬ p343) ∨ (¬ p536) ∨ (¬ p544) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p940) ∨ p1324 ∨ (¬ p1325)) : (¬ p239) ∨ (¬ p536) ∨ (¬ p544) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p940) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p239 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p544 := by
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
  have u5 : p940 := by
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
  rcases h14512 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19150 (p7 p125 p264 p303 p519 p789 : Prop)
    (h16152 : (¬ p7))
    (h14513 : p7 ∨ (¬ p125) ∨ (¬ p264) ∨ (¬ p303) ∨ (¬ p519) ∨ (¬ p789)) : (¬ p125) ∨ (¬ p264) ∨ (¬ p303) ∨ (¬ p519) ∨ (¬ p789) := by
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
  have u2 : p303 := by
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
  rcases h14513 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19151 (p7 p11 p125 p126 p239 p261 p534 p1036 p1061 p1445 p1603 : Prop)
    (h16152 : (¬ p7))
    (h16350 : (¬ p1445))
    (h9837 : p1603)
    (h14515 : p7 ∨ (¬ p11) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p239) ∨ (¬ p261) ∨ (¬ p534) ∨ (¬ p1036) ∨ (¬ p1061) ∨ p1445 ∨ (¬ p1603)) : (¬ p11) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p239) ∨ (¬ p261) ∨ (¬ p534) ∨ (¬ p1036) ∨ (¬ p1061) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
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
  have u3 : p239 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p1445) := by
    exact h16350
  have u10 : p1603 := by
    exact h9837
  rcases h14515 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (u9 q9)
  · exact False.elim (q10 u10)

theorem step19152 (p3 p7 p11 p12 p13 p26 p68 p125 p126 p425 : Prop)
    (h16152 : (¬ p7))
    (h14516 : (¬ p3) ∨ p7 ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p13) ∨ (¬ p26) ∨ (¬ p68) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p425)) : (¬ p3) ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p13) ∨ (¬ p26) ∨ (¬ p68) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p425) := by
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
  have u2 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p26 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14516 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19153 (p7 p11 p125 p126 p239 p261 p343 p536 p544 p940 p1445 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16350 : (¬ p1445))
    (h14517 : p7 ∨ (¬ p11) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p239) ∨ (¬ p261) ∨ (¬ p343) ∨ (¬ p536) ∨ (¬ p544) ∨ (¬ p940) ∨ p1445) : (¬ p11) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p239) ∨ (¬ p261) ∨ (¬ p536) ∨ (¬ p544) ∨ (¬ p940) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
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
  have u3 : p239 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p343 := by
    exact h1950
  have u10 : (¬ p1445) := by
    exact h16350
  rcases h14517 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19154 (p7 p458 p499 p578 p1232 p1443 : Prop)
    (h16152 : (¬ p7))
    (h14518 : p7 ∨ (¬ p458) ∨ (¬ p499) ∨ (¬ p578) ∨ (¬ p1232) ∨ (¬ p1443)) : (¬ p458) ∨ (¬ p499) ∨ (¬ p578) ∨ (¬ p1232) ∨ (¬ p1443) := by
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
  have u2 : p578 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14518 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19155 (p7 p126 p264 p363 p434 p690 : Prop)
    (h16152 : (¬ p7))
    (h14519 : p7 ∨ (¬ p126) ∨ (¬ p264) ∨ (¬ p363) ∨ (¬ p434) ∨ (¬ p690)) : (¬ p126) ∨ (¬ p264) ∨ (¬ p363) ∨ (¬ p434) ∨ (¬ p690) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p264 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p363 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14519 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19156 (p7 p39 p69 p425 p532 p575 p961 p1229 p1291 p1333 : Prop)
    (h16152 : (¬ p7))
    (h14520 : p7 ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p425) ∨ (¬ p532) ∨ (¬ p575) ∨ (¬ p961) ∨ (¬ p1229) ∨ (¬ p1291) ∨ (¬ p1333)) : (¬ p39) ∨ (¬ p69) ∨ (¬ p425) ∨ (¬ p532) ∨ (¬ p575) ∨ (¬ p961) ∨ (¬ p1229) ∨ (¬ p1291) ∨ (¬ p1333) := by
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
  have u2 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p575 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p961 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14520 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19157 (p3 p7 p190 p533 p534 p814 p858 p1325 : Prop)
    (h16152 : (¬ p7))
    (h14521 : (¬ p3) ∨ p7 ∨ (¬ p190) ∨ (¬ p533) ∨ (¬ p534) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1325)) : (¬ p3) ∨ (¬ p190) ∨ (¬ p533) ∨ (¬ p534) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p534 := by
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
  rcases h14521 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19158 (p7 p39 p69 p125 p126 p258 p343 p425 p544 p575 p686 p883 p1096 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16205 : (¬ p686))
    (h14522 : p7 ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p258) ∨ (¬ p343) ∨ (¬ p425) ∨ (¬ p544) ∨ (¬ p575) ∨ p686 ∨ (¬ p883) ∨ (¬ p1096)) : (¬ p39) ∨ (¬ p69) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p258) ∨ (¬ p425) ∨ (¬ p544) ∨ (¬ p575) ∨ (¬ p883) ∨ (¬ p1096) := by
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
  have u2 : p125 := by
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
  have u5 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p575 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : p343 := by
    exact h1950
  have u12 : (¬ p686) := by
    exact h16205
  rcases h14522 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (u12 q10)
  · exact False.elim (q11 u8)
  · exact False.elim (q12 u9)

theorem step19159 (p7 p256 p302 p303 p515 p576 p792 p814 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h4535 : p792)
    (h14523 : p7 ∨ (¬ p256) ∨ p302 ∨ (¬ p303) ∨ (¬ p515) ∨ (¬ p576) ∨ (¬ p792) ∨ (¬ p814)) : (¬ p256) ∨ (¬ p303) ∨ (¬ p515) ∨ (¬ p576) ∨ (¬ p814) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p256 := by
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
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p302) := by
    exact h16285
  have u7 : p792 := by
    exact h4535
  rcases h14523 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step19160 (p7 p129 p189 p242 p343 p544 p1036 p1061 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h1950 : p343)
    (h14524 : p7 ∨ p129 ∨ (¬ p189) ∨ (¬ p242) ∨ (¬ p343) ∨ (¬ p544) ∨ (¬ p1036) ∨ (¬ p1061)) : (¬ p189) ∨ (¬ p242) ∨ (¬ p544) ∨ (¬ p1036) ∨ (¬ p1061) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p544 := by
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
  have u7 : p343 := by
    exact h1950
  rcases h14524 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step19161 (p7 p135 p187 p561 p581 p922 p1061 p1074 : Prop)
    (h16152 : (¬ p7))
    (h14525 : p7 ∨ (¬ p135) ∨ (¬ p187) ∨ (¬ p561) ∨ (¬ p581) ∨ (¬ p922) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p135) ∨ (¬ p187) ∨ (¬ p561) ∨ (¬ p581) ∨ (¬ p922) ∨ (¬ p1061) ∨ (¬ p1074) := by
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
  have u2 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p922 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14525 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19162 (p7 p343 p544 p1036 p1095 p1096 p1136 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16259 : (¬ p1136))
    (h14526 : p7 ∨ (¬ p343) ∨ (¬ p544) ∨ (¬ p1036) ∨ (¬ p1095) ∨ (¬ p1096) ∨ p1136) : (¬ p544) ∨ (¬ p1036) ∨ (¬ p1095) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1036 := by
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
  have u5 : p343 := by
    exact h1950
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h14526 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step19163 (p7 p302 p343 p544 p980 p1036 p1333 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h1950 : p343)
    (h14527 : p7 ∨ p302 ∨ (¬ p343) ∨ (¬ p544) ∨ (¬ p980) ∨ (¬ p1036) ∨ (¬ p1333)) : (¬ p544) ∨ (¬ p980) ∨ (¬ p1036) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p544 := by
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
  have u3 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p302) := by
    exact h16285
  have u6 : p343 := by
    exact h1950
  rcases h14527 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19164 (p7 p14 p15 p125 p303 p343 p500 p544 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16309 : (¬ p1324))
    (h14528 : p7 ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p125) ∨ (¬ p303) ∨ (¬ p343) ∨ (¬ p500) ∨ (¬ p544) ∨ p1324 ∨ (¬ p1325)) : (¬ p14) ∨ (¬ p15) ∨ (¬ p125) ∨ (¬ p303) ∨ (¬ p500) ∨ (¬ p544) ∨ (¬ p1325) := by
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
  have u2 : p125 := by
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
  have u5 : p544 := by
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
  rcases h14528 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19165 (p7 p544 p664 p983 p1037 p1465 : Prop)
    (h16152 : (¬ p7))
    (h14529 : p7 ∨ (¬ p544) ∨ (¬ p664) ∨ (¬ p983) ∨ (¬ p1037) ∨ (¬ p1465)) : (¬ p544) ∨ (¬ p664) ∨ (¬ p983) ∨ (¬ p1037) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p664 := by
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
  rcases h14529 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19166 (p7 p265 p302 p303 p363 p434 p576 p690 p792 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h4535 : p792)
    (h14530 : p7 ∨ (¬ p265) ∨ p302 ∨ (¬ p303) ∨ (¬ p363) ∨ (¬ p434) ∨ (¬ p576) ∨ (¬ p690) ∨ (¬ p792)) : (¬ p265) ∨ (¬ p303) ∨ (¬ p363) ∨ (¬ p434) ∨ (¬ p576) ∨ (¬ p690) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p363 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p302) := by
    exact h16285
  have u8 : p792 := by
    exact h4535
  rcases h14530 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u8)

theorem step19167 (p3 p7 p12 p39 p68 p301 p303 p576 p665 : Prop)
    (h16152 : (¬ p7))
    (h14531 : (¬ p3) ∨ p7 ∨ (¬ p12) ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p576) ∨ (¬ p665)) : (¬ p3) ∨ (¬ p12) ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p576) ∨ (¬ p665) := by
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
  have u3 : p68 := by
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
  have u6 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14531 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19169 (p7 p24 p39 p69 p88 p323 p382 p499 p521 p789 p815 : Prop)
    (h16152 : (¬ p7))
    (h14533 : p7 ∨ (¬ p24) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p323) ∨ (¬ p382) ∨ (¬ p499) ∨ (¬ p521) ∨ (¬ p789) ∨ (¬ p815)) : (¬ p24) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p323) ∨ (¬ p382) ∨ (¬ p499) ∨ (¬ p521) ∨ (¬ p789) ∨ (¬ p815) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p24 := by
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
  have u4 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p521 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p815 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h14533 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19170 (p7 p12 p39 p69 p88 p665 p814 p858 p883 p1096 : Prop)
    (h16152 : (¬ p7))
    (h14534 : p7 ∨ (¬ p12) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p665) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p883) ∨ (¬ p1096)) : (¬ p12) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p665) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p883) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
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
  have u4 : p665 := by
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
  rcases h14534 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19171 (p7 p229 p234 p543 p664 p1036 : Prop)
    (h16152 : (¬ p7))
    (h14535 : p7 ∨ (¬ p229) ∨ (¬ p234) ∨ (¬ p543) ∨ (¬ p664) ∨ (¬ p1036)) : (¬ p229) ∨ (¬ p234) ∨ (¬ p543) ∨ (¬ p664) ∨ (¬ p1036) := by
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
  have u2 : p543 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14535 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19172 (p7 p224 p304 p343 p362 p387 p686 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16205 : (¬ p686))
    (h14537 : p7 ∨ (¬ p224) ∨ (¬ p304) ∨ (¬ p343) ∨ (¬ p362) ∨ (¬ p387) ∨ p686) : (¬ p224) ∨ (¬ p304) ∨ (¬ p362) ∨ (¬ p387) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
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
  have u3 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p343 := by
    exact h1950
  have u6 : (¬ p686) := by
    exact h16205
  rcases h14537 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step19173 (p7 p15 p16 p423 p814 p1015 p1035 p1335 : Prop)
    (h16152 : (¬ p7))
    (h14538 : p7 ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p423) ∨ (¬ p814) ∨ (¬ p1015) ∨ (¬ p1035) ∨ (¬ p1335)) : (¬ p15) ∨ (¬ p16) ∨ (¬ p423) ∨ (¬ p814) ∨ (¬ p1015) ∨ (¬ p1035) ∨ (¬ p1335) := by
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
  have u2 : p423 := by
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
  have u5 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14538 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19174 (p7 p12 p14 p15 p790 p792 p1124 p1136 p1349 p1385 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16259 : (¬ p1136))
    (h14539 : p7 ∨ (¬ p12) ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p790) ∨ (¬ p792) ∨ (¬ p1124) ∨ p1136 ∨ (¬ p1349) ∨ (¬ p1385)) : (¬ p12) ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p790) ∨ (¬ p1124) ∨ (¬ p1349) ∨ (¬ p1385) := by
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
  have u3 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p792 := by
    exact h4535
  have u9 : (¬ p1136) := by
    exact h16259
  rcases h14539 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19175 (p7 p126 p185 p255 p256 p350 : Prop)
    (h16152 : (¬ p7))
    (h14541 : p7 ∨ (¬ p126) ∨ (¬ p185) ∨ (¬ p255) ∨ (¬ p256) ∨ (¬ p350)) : (¬ p126) ∨ (¬ p185) ∨ (¬ p255) ∨ (¬ p256) ∨ (¬ p350) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14541 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19176 (p7 p43 p163 p229 p802 p1393 : Prop)
    (h16152 : (¬ p7))
    (h14542 : p7 ∨ (¬ p43) ∨ (¬ p163) ∨ (¬ p229) ∨ (¬ p802) ∨ (¬ p1393)) : (¬ p43) ∨ (¬ p163) ∨ (¬ p229) ∨ (¬ p802) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p229 := by
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
  rcases h14542 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19177 (p7 p163 p188 p226 p790 p802 : Prop)
    (h16152 : (¬ p7))
    (h14543 : p7 ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p790) ∨ (¬ p802)) : (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p790) ∨ (¬ p802) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p802 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14543 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19178 (p7 p123 p261 p288 p304 p790 p792 p1385 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h4535 : p792)
    (h14544 : p7 ∨ p123 ∨ (¬ p261) ∨ (¬ p288) ∨ (¬ p304) ∨ (¬ p790) ∨ (¬ p792) ∨ (¬ p1385)) : (¬ p261) ∨ (¬ p288) ∨ (¬ p304) ∨ (¬ p790) ∨ (¬ p1385) := by
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
  have u2 : p304 := by
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
  have u6 : (¬ p123) := by
    exact h16186
  have u7 : p792 := by
    exact h4535
  rcases h14544 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step19179 (p7 p499 p633 p790 p792 p1077 p1124 p1136 p1349 p1385 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16259 : (¬ p1136))
    (h14545 : p7 ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p790) ∨ (¬ p792) ∨ (¬ p1077) ∨ (¬ p1124) ∨ p1136 ∨ (¬ p1349) ∨ (¬ p1385)) : (¬ p499) ∨ (¬ p633) ∨ (¬ p790) ∨ (¬ p1077) ∨ (¬ p1124) ∨ (¬ p1349) ∨ (¬ p1385) := by
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
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p792 := by
    exact h4535
  have u9 : (¬ p1136) := by
    exact h16259
  rcases h14545 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19182 (p7 p103 p129 p169 p189 p242 p323 p427 p536 p1584 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h2334 : p427)
    (h14548 : p7 ∨ (¬ p103) ∨ p129 ∨ (¬ p169) ∨ (¬ p189) ∨ (¬ p242) ∨ (¬ p323) ∨ (¬ p427) ∨ (¬ p536) ∨ (¬ p1584)) : (¬ p103) ∨ (¬ p169) ∨ (¬ p189) ∨ (¬ p242) ∨ (¬ p323) ∨ (¬ p536) ∨ (¬ p1584) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p103 := by
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
  have u3 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p129) := by
    exact h16154
  have u9 : p427 := by
    exact h2334
  rcases h14548 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u8 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step19183 (p7 p129 p189 p1346 p1465 p1508 p1708 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h10766 : p1708)
    (h14550 : p7 ∨ p129 ∨ (¬ p189) ∨ (¬ p1346) ∨ (¬ p1465) ∨ (¬ p1508) ∨ (¬ p1708)) : (¬ p189) ∨ (¬ p1346) ∨ (¬ p1465) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1465 := by
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
  have u6 : p1708 := by
    exact h10766
  rcases h14550 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19184 (p7 p129 p189 p237 p323 p427 p665 p1116 p1167 p1207 p1226 p1333 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h2334 : p427)
    (h14551 : p7 ∨ p129 ∨ (¬ p189) ∨ (¬ p237) ∨ (¬ p323) ∨ (¬ p427) ∨ (¬ p665) ∨ (¬ p1116) ∨ (¬ p1167) ∨ (¬ p1207) ∨ (¬ p1226) ∨ (¬ p1333)) : (¬ p189) ∨ (¬ p237) ∨ (¬ p323) ∨ (¬ p665) ∨ (¬ p1116) ∨ (¬ p1167) ∨ (¬ p1207) ∨ (¬ p1226) ∨ (¬ p1333) := by
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
  have u2 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p129) := by
    exact h16154
  have u11 : p427 := by
    exact h2334
  rcases h14551 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (u10 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step19185 (p7 p101 p323 p427 p499 p633 p1136 : Prop)
    (h16152 : (¬ p7))
    (h2334 : p427)
    (h16259 : (¬ p1136))
    (h14552 : p7 ∨ (¬ p101) ∨ (¬ p323) ∨ (¬ p427) ∨ (¬ p499) ∨ (¬ p633) ∨ p1136) : (¬ p101) ∨ (¬ p323) ∨ (¬ p499) ∨ (¬ p633) := by
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
  have u5 : p427 := by
    exact h2334
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h14552 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step19186 (p7 p14 p15 p382 p533 p534 p792 p819 p1136 p1325 p1385 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16259 : (¬ p1136))
    (h14554 : p7 ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p382) ∨ (¬ p533) ∨ (¬ p534) ∨ (¬ p792) ∨ (¬ p819) ∨ p1136 ∨ (¬ p1325) ∨ (¬ p1385)) : (¬ p14) ∨ (¬ p15) ∨ (¬ p382) ∨ (¬ p533) ∨ (¬ p534) ∨ (¬ p819) ∨ (¬ p1325) ∨ (¬ p1385) := by
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
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p819 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p792 := by
    exact h4535
  have u10 : (¬ p1136) := by
    exact h16259
  rcases h14554 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19187 (p7 p17 p143 p1206 p1346 p1495 : Prop)
    (h16152 : (¬ p7))
    (h14555 : p7 ∨ (¬ p17) ∨ (¬ p143) ∨ (¬ p1206) ∨ (¬ p1346) ∨ (¬ p1495)) : (¬ p17) ∨ (¬ p143) ∨ (¬ p1206) ∨ (¬ p1346) ∨ (¬ p1495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14555 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19188 (p7 p19 p129 p163 p229 p323 p427 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h2334 : p427)
    (h14556 : p7 ∨ (¬ p19) ∨ p129 ∨ (¬ p163) ∨ (¬ p229) ∨ (¬ p323) ∨ (¬ p427)) : (¬ p19) ∨ (¬ p163) ∨ (¬ p229) ∨ (¬ p323) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p427 := by
    exact h2334
  rcases h14556 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19189 (p3 p7 p72 p665 p880 p997 p1095 p1187 p1333 p1465 : Prop)
    (h16152 : (¬ p7))
    (h14557 : (¬ p3) ∨ p7 ∨ (¬ p72) ∨ (¬ p665) ∨ (¬ p880) ∨ (¬ p997) ∨ (¬ p1095) ∨ (¬ p1187) ∨ (¬ p1333) ∨ (¬ p1465)) : (¬ p3) ∨ (¬ p72) ∨ (¬ p665) ∨ (¬ p880) ∨ (¬ p997) ∨ (¬ p1095) ∨ (¬ p1187) ∨ (¬ p1333) ∨ (¬ p1465) := by
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
  have u2 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p997 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1187 := by
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
  rcases h14557 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19190 (p7 p18 p46 p141 p210 p288 p304 : Prop)
    (h16152 : (¬ p7))
    (h14558 : p7 ∨ (¬ p18) ∨ (¬ p46) ∨ (¬ p141) ∨ (¬ p210) ∨ (¬ p288) ∨ (¬ p304)) : (¬ p18) ∨ (¬ p46) ∨ (¬ p141) ∨ (¬ p210) ∨ (¬ p288) ∨ (¬ p304) := by
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
  have u4 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14558 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19191 (p7 p10 p18 p46 p126 p141 : Prop)
    (h16152 : (¬ p7))
    (h14559 : p7 ∨ (¬ p10) ∨ (¬ p18) ∨ (¬ p46) ∨ (¬ p126) ∨ (¬ p141)) : (¬ p10) ∨ (¬ p18) ∨ (¬ p46) ∨ (¬ p126) ∨ (¬ p141) := by
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
  have u2 : p46 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14559 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19193 (p7 p16 p17 p18 p71 p127 p234 p258 p328 p350 : Prop)
    (h16152 : (¬ p7))
    (h14561 : p7 ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p18) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p234) ∨ (¬ p258) ∨ (¬ p328) ∨ (¬ p350)) : (¬ p16) ∨ (¬ p17) ∨ (¬ p18) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p234) ∨ (¬ p258) ∨ (¬ p328) ∨ (¬ p350) := by
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
  have u5 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p328 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14561 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19195 (p7 p16 p814 p983 p1015 p1095 p1096 p1335 : Prop)
    (h16152 : (¬ p7))
    (h14563 : p7 ∨ (¬ p16) ∨ (¬ p814) ∨ (¬ p983) ∨ (¬ p1015) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1335)) : (¬ p16) ∨ (¬ p814) ∨ (¬ p983) ∨ (¬ p1015) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1335) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
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
  have u3 : p1015 := by
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
  have u6 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14563 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19196 (p7 p72 p480 p665 p816 p858 p980 p1035 p1140 p1187 : Prop)
    (h16152 : (¬ p7))
    (h14564 : p7 ∨ (¬ p72) ∨ (¬ p480) ∨ (¬ p665) ∨ (¬ p816) ∨ (¬ p858) ∨ (¬ p980) ∨ (¬ p1035) ∨ (¬ p1140) ∨ (¬ p1187)) : (¬ p72) ∨ (¬ p480) ∨ (¬ p665) ∨ (¬ p816) ∨ (¬ p858) ∨ (¬ p980) ∨ (¬ p1035) ∨ (¬ p1140) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p480 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p858 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14564 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19197 (p7 p46 p158 p170 p229 p536 p940 : Prop)
    (h16152 : (¬ p7))
    (h14565 : p7 ∨ (¬ p46) ∨ (¬ p158) ∨ (¬ p170) ∨ (¬ p229) ∨ (¬ p536) ∨ (¬ p940)) : (¬ p46) ∨ (¬ p158) ∨ (¬ p170) ∨ (¬ p229) ∨ (¬ p536) ∨ (¬ p940) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p46 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14565 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19198 (p3 p7 p16 p19 p71 p229 p788 p814 p858 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h5066 : p788)
    (h16309 : (¬ p1324))
    (h14566 : (¬ p3) ∨ p7 ∨ (¬ p16) ∨ (¬ p19) ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p788) ∨ (¬ p814) ∨ (¬ p858) ∨ p1324 ∨ (¬ p1325)) : (¬ p3) ∨ (¬ p16) ∨ (¬ p19) ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1325) := by
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
  have u2 : p19 := by
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
  have u9 : p788 := by
    exact h5066
  have u10 : (¬ p1324) := by
    exact h16309
  rcases h14566 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (u10 q9)
  · exact False.elim (q10 u7)

theorem step19199 (p7 p258 p262 p362 p434 p686 p1545 p1664 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h10244 : p1664)
    (h14567 : p7 ∨ (¬ p258) ∨ (¬ p262) ∨ (¬ p362) ∨ (¬ p434) ∨ p686 ∨ (¬ p1545) ∨ (¬ p1664)) : (¬ p258) ∨ (¬ p262) ∨ (¬ p362) ∨ (¬ p434) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p262 := by
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
  have u4 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p686) := by
    exact h16205
  have u7 : p1664 := by
    exact h10244
  rcases h14567 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step19200 (p3 p7 p16 p71 p229 p814 p858 p1193 p1334 p1542 : Prop)
    (h16152 : (¬ p7))
    (h14568 : (¬ p3) ∨ p7 ∨ (¬ p16) ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1193) ∨ (¬ p1334) ∨ (¬ p1542)) : (¬ p3) ∨ (¬ p16) ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1193) ∨ (¬ p1334) ∨ (¬ p1542) := by
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
  have u3 : p229 := by
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
  have u6 : p1193 := by
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
  rcases h14568 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19201 (p7 p16 p665 p814 p858 p980 p1096 p1225 p1311 : Prop)
    (h16152 : (¬ p7))
    (h14569 : p7 ∨ (¬ p16) ∨ (¬ p665) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p980) ∨ (¬ p1096) ∨ (¬ p1225) ∨ (¬ p1311)) : (¬ p16) ∨ (¬ p665) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p980) ∨ (¬ p1096) ∨ (¬ p1225) ∨ (¬ p1311) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p665 := by
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
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1311 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14569 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19202 (p3 p7 p71 p229 p362 p420 p423 p961 p1136 p1210 p1530 : Prop)
    (h16152 : (¬ p7))
    (h16259 : (¬ p1136))
    (h9352 : p1530)
    (h14571 : (¬ p3) ∨ p7 ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p423) ∨ (¬ p961) ∨ p1136 ∨ (¬ p1210) ∨ (¬ p1530)) : (¬ p3) ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p423) ∨ (¬ p961) ∨ (¬ p1210) := by
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
  have u3 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p1136) := by
    exact h16259
  have u10 : p1530 := by
    exact h9352
  rcases h14571 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19203 (p7 p233 p234 p302 p1141 p1333 p1465 : Prop)
    (h16152 : (¬ p7))
    (h2345 : p233)
    (h16285 : (¬ p302))
    (h14572 : p7 ∨ (¬ p233) ∨ (¬ p234) ∨ p302 ∨ (¬ p1141) ∨ (¬ p1333) ∨ (¬ p1465)) : (¬ p234) ∨ (¬ p1141) ∨ (¬ p1333) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1141 := by
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
  have u5 : p233 := by
    exact h2345
  have u6 : (¬ p302) := by
    exact h16285
  rcases h14572 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19204 (p7 p12 p14 p15 p16 p665 p814 p858 : Prop)
    (h16152 : (¬ p7))
    (h14573 : p7 ∨ (¬ p12) ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p665) ∨ (¬ p814) ∨ (¬ p858)) : (¬ p12) ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p665) ∨ (¬ p814) ∨ (¬ p858) := by
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
  have u4 : p665 := by
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
  rcases h14573 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19205 (p7 p15 p16 p234 p327 p387 p814 p858 : Prop)
    (h16152 : (¬ p7))
    (h14574 : p7 ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p234) ∨ (¬ p327) ∨ (¬ p387) ∨ (¬ p814) ∨ (¬ p858)) : (¬ p15) ∨ (¬ p16) ∨ (¬ p234) ∨ (¬ p327) ∨ (¬ p387) ∨ (¬ p814) ∨ (¬ p858) := by
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
  have u3 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p387 := by
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
  rcases h14574 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19206 (p7 p8 p72 p225 p229 p561 : Prop)
    (h16152 : (¬ p7))
    (h14575 : p7 ∨ (¬ p8) ∨ (¬ p72) ∨ (¬ p225) ∨ (¬ p229) ∨ (¬ p561)) : (¬ p8) ∨ (¬ p72) ∨ (¬ p225) ∨ (¬ p229) ∨ (¬ p561) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p72 := by
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
  have u4 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14575 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19208 (p7 p157 p158 p160 p172 p980 p1036 : Prop)
    (h16152 : (¬ p7))
    (h14577 : p7 ∨ (¬ p157) ∨ (¬ p158) ∨ (¬ p160) ∨ (¬ p172) ∨ (¬ p980) ∨ (¬ p1036)) : (¬ p157) ∨ (¬ p158) ∨ (¬ p160) ∨ (¬ p172) ∨ (¬ p980) ∨ (¬ p1036) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p157 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14577 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19209 (p7 p8 p39 p63 p68 p561 p616 p728 p858 p1334 p1388 : Prop)
    (h16152 : (¬ p7))
    (h14578 : p7 ∨ (¬ p8) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p561) ∨ (¬ p616) ∨ (¬ p728) ∨ (¬ p858) ∨ (¬ p1334) ∨ (¬ p1388)) : (¬ p8) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p561) ∨ (¬ p616) ∨ (¬ p728) ∨ (¬ p858) ∨ (¬ p1334) ∨ (¬ p1388) := by
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
  have u4 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1388 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h14578 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19210 (p7 p280 p434 p499 p616 p1530 p1545 : Prop)
    (h16152 : (¬ p7))
    (h16173 : (¬ p280))
    (h9352 : p1530)
    (h14579 : p7 ∨ p280 ∨ (¬ p434) ∨ (¬ p499) ∨ (¬ p616) ∨ (¬ p1530) ∨ (¬ p1545)) : (¬ p434) ∨ (¬ p499) ∨ (¬ p616) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p280) := by
    exact h16173
  have u6 : p1530 := by
    exact h9352
  rcases h14579 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step19211 (p7 p39 p63 p68 p561 p616 p983 p1015 p1061 p1335 p1388 : Prop)
    (h16152 : (¬ p7))
    (h14580 : p7 ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p561) ∨ (¬ p616) ∨ (¬ p983) ∨ (¬ p1015) ∨ (¬ p1061) ∨ (¬ p1335) ∨ (¬ p1388)) : (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p561) ∨ (¬ p616) ∨ (¬ p983) ∨ (¬ p1015) ∨ (¬ p1061) ∨ (¬ p1335) ∨ (¬ p1388) := by
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
  have u4 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1388 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h14580 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19212 (p7 p135 p256 p382 p789 p795 p815 : Prop)
    (h16152 : (¬ p7))
    (h14581 : p7 ∨ (¬ p135) ∨ (¬ p256) ∨ (¬ p382) ∨ (¬ p789) ∨ (¬ p795) ∨ (¬ p815)) : (¬ p135) ∨ (¬ p256) ∨ (¬ p382) ∨ (¬ p789) ∨ (¬ p795) ∨ (¬ p815) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p795 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p815 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14581 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19213 (p7 p132 p256 p814 p858 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16309 : (¬ p1324))
    (h14582 : p7 ∨ (¬ p132) ∨ (¬ p256) ∨ (¬ p814) ∨ (¬ p858) ∨ p1324 ∨ (¬ p1325)) : (¬ p256) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p256 := by
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
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p132 := by
    exact h786
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h14582 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step19214 (p7 p45 p103 p193 p225 p788 p791 p833 p1393 : Prop)
    (h16152 : (¬ p7))
    (h5066 : p788)
    (h16213 : (¬ p791))
    (h14583 : p7 ∨ (¬ p45) ∨ (¬ p103) ∨ (¬ p193) ∨ (¬ p225) ∨ (¬ p788) ∨ p791 ∨ (¬ p833) ∨ (¬ p1393)) : (¬ p45) ∨ (¬ p103) ∨ (¬ p193) ∨ (¬ p225) ∨ (¬ p833) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p833 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : p788 := by
    exact h5066
  have u8 : (¬ p791) := by
    exact h16213
  rcases h14583 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u7)
  · exact False.elim (u8 q6)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step19215 (p7 p132 p237 p382 p581 p728 p791 p819 p840 p1334 p1385 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16213 : (¬ p791))
    (h14584 : p7 ∨ (¬ p132) ∨ (¬ p237) ∨ (¬ p382) ∨ (¬ p581) ∨ (¬ p728) ∨ p791 ∨ (¬ p819) ∨ (¬ p840) ∨ (¬ p1334) ∨ (¬ p1385)) : (¬ p237) ∨ (¬ p382) ∨ (¬ p581) ∨ (¬ p728) ∨ (¬ p819) ∨ (¬ p840) ∨ (¬ p1334) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p819 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p840 := by
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
  have u9 : p132 := by
    exact h786
  have u10 : (¬ p791) := by
    exact h16213
  rcases h14584 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19216 (p7 p106 p225 p662 p980 p1083 p1452 : Prop)
    (h16152 : (¬ p7))
    (h14585 : p7 ∨ (¬ p106) ∨ (¬ p225) ∨ (¬ p662) ∨ (¬ p980) ∨ (¬ p1083) ∨ (¬ p1452)) : (¬ p106) ∨ (¬ p225) ∨ (¬ p662) ∨ (¬ p980) ∨ (¬ p1083) ∨ (¬ p1452) := by
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
  have u2 : p662 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1083 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14585 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19217 (p7 p90 p106 p225 p237 p265 p304 p576 p840 : Prop)
    (h16152 : (¬ p7))
    (h14586 : p7 ∨ (¬ p90) ∨ (¬ p106) ∨ (¬ p225) ∨ (¬ p237) ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p576) ∨ (¬ p840)) : (¬ p90) ∨ (¬ p106) ∨ (¬ p225) ∨ (¬ p237) ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p576) ∨ (¬ p840) := by
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
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14586 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19218 (p7 p132 p382 p581 p819 p1324 p1325 p1385 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16309 : (¬ p1324))
    (h14587 : p7 ∨ (¬ p132) ∨ (¬ p382) ∨ (¬ p581) ∨ (¬ p819) ∨ p1324 ∨ (¬ p1325) ∨ (¬ p1385)) : (¬ p382) ∨ (¬ p581) ∨ (¬ p819) ∨ (¬ p1325) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p819 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p132 := by
    exact h786
  have u7 : (¬ p1324) := by
    exact h16309
  rcases h14587 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u7 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step19219 (p7 p132 p237 p581 p791 p983 p1015 p1116 p1335 p1385 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16213 : (¬ p791))
    (h14588 : p7 ∨ (¬ p132) ∨ (¬ p237) ∨ (¬ p581) ∨ p791 ∨ (¬ p983) ∨ (¬ p1015) ∨ (¬ p1116) ∨ (¬ p1335) ∨ (¬ p1385)) : (¬ p237) ∨ (¬ p581) ∨ (¬ p983) ∨ (¬ p1015) ∨ (¬ p1116) ∨ (¬ p1335) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p983 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p132 := by
    exact h786
  have u9 : (¬ p791) := by
    exact h16213
  rcases h14588 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (u9 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step19220 (p7 p172 p185 p225 p790 p833 : Prop)
    (h16152 : (¬ p7))
    (h14589 : p7 ∨ (¬ p172) ∨ (¬ p185) ∨ (¬ p225) ∨ (¬ p790) ∨ (¬ p833)) : (¬ p172) ∨ (¬ p185) ∨ (¬ p225) ∨ (¬ p790) ∨ (¬ p833) := by
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
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p833 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14589 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19221 (p7 p8 p88 p135 p187 p561 p581 p728 p814 p858 p1334 : Prop)
    (h16152 : (¬ p7))
    (h14590 : p7 ∨ (¬ p8) ∨ (¬ p88) ∨ (¬ p135) ∨ (¬ p187) ∨ (¬ p561) ∨ (¬ p581) ∨ (¬ p728) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1334)) : (¬ p8) ∨ (¬ p88) ∨ (¬ p135) ∨ (¬ p187) ∨ (¬ p561) ∨ (¬ p581) ∨ (¬ p728) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1334) := by
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
  have u2 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p728 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h14590 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19222 (p7 p132 p302 p581 p858 p1022 p1387 p1545 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16285 : (¬ p302))
    (h14591 : p7 ∨ (¬ p132) ∨ p302 ∨ (¬ p581) ∨ (¬ p858) ∨ (¬ p1022) ∨ (¬ p1387) ∨ (¬ p1545)) : (¬ p581) ∨ (¬ p858) ∨ (¬ p1022) ∨ (¬ p1387) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p581 := by
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
  have u3 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p132 := by
    exact h786
  have u7 : (¬ p302) := by
    exact h16285
  rcases h14591 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step19223 (p7 p135 p158 p170 p581 p922 p1061 p1074 : Prop)
    (h16152 : (¬ p7))
    (h14592 : p7 ∨ (¬ p135) ∨ (¬ p158) ∨ (¬ p170) ∨ (¬ p581) ∨ (¬ p922) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p135) ∨ (¬ p158) ∨ (¬ p170) ∨ (¬ p581) ∨ (¬ p922) ∨ (¬ p1061) ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p922 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14592 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19224 (p7 p132 p256 p302 p532 p814 p856 p1333 p1493 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16285 : (¬ p302))
    (h14593 : p7 ∨ (¬ p132) ∨ (¬ p256) ∨ p302 ∨ (¬ p532) ∨ (¬ p814) ∨ (¬ p856) ∨ (¬ p1333) ∨ (¬ p1493)) : (¬ p256) ∨ (¬ p532) ∨ (¬ p814) ∨ (¬ p856) ∨ (¬ p1333) ∨ (¬ p1493) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p856 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1493 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : p132 := by
    exact h786
  have u8 : (¬ p302) := by
    exact h16285
  rcases h14593 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u0)
  · exact False.elim (u8 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step19225 (p7 p106 p126 p225 p258 p364 p713 : Prop)
    (h16152 : (¬ p7))
    (h14594 : p7 ∨ (¬ p106) ∨ (¬ p126) ∨ (¬ p225) ∨ (¬ p258) ∨ (¬ p364) ∨ (¬ p713)) : (¬ p106) ∨ (¬ p126) ∨ (¬ p225) ∨ (¬ p258) ∨ (¬ p364) ∨ (¬ p713) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p713 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14594 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19226 (p7 p15 p16 p17 p301 p303 p423 p1000 : Prop)
    (h16152 : (¬ p7))
    (h14595 : p7 ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p423) ∨ (¬ p1000)) : (¬ p15) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p423) ∨ (¬ p1000) := by
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
  have u3 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14595 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19227 (p7 p19 p44 p90 p121 p193 p228 p858 p1385 : Prop)
    (h16152 : (¬ p7))
    (h14596 : p7 ∨ (¬ p19) ∨ (¬ p44) ∨ (¬ p90) ∨ (¬ p121) ∨ (¬ p193) ∨ (¬ p228) ∨ (¬ p858) ∨ (¬ p1385)) : (¬ p19) ∨ (¬ p44) ∨ (¬ p90) ∨ (¬ p121) ∨ (¬ p193) ∨ (¬ p228) ∨ (¬ p858) ∨ (¬ p1385) := by
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
  have u2 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14596 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19228 (p7 p288 p302 p581 p858 p1075 p1385 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h6478 : p1075)
    (h14598 : p7 ∨ (¬ p288) ∨ p302 ∨ (¬ p581) ∨ (¬ p858) ∨ (¬ p1075) ∨ (¬ p1385)) : (¬ p288) ∨ (¬ p581) ∨ (¬ p858) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p581 := by
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
  have u5 : (¬ p302) := by
    exact h16285
  have u6 : p1075 := by
    exact h6478
  rcases h14598 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step19229 (p7 p87 p261 p288 p304 p581 : Prop)
    (h16152 : (¬ p7))
    (h14600 : p7 ∨ (¬ p87) ∨ (¬ p261) ∨ (¬ p288) ∨ (¬ p304) ∨ (¬ p581)) : (¬ p87) ∨ (¬ p261) ∨ (¬ p288) ∨ (¬ p304) ∨ (¬ p581) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p261 := by
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
  have u4 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14600 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19230 (p7 p27 p103 p306 p536 p633 p940 : Prop)
    (h16152 : (¬ p7))
    (h14601 : p7 ∨ (¬ p27) ∨ (¬ p103) ∨ (¬ p306) ∨ (¬ p536) ∨ (¬ p633) ∨ (¬ p940)) : (¬ p27) ∨ (¬ p103) ∨ (¬ p306) ∨ (¬ p536) ∨ (¬ p633) ∨ (¬ p940) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p27 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14601 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19231 (p7 p161 p227 p304 p367 p382 p427 p633 p1160 p1292 p1442 p1508 : Prop)
    (h16152 : (¬ p7))
    (h2334 : p427)
    (h16265 : (¬ p1160))
    (h14602 : p7 ∨ (¬ p161) ∨ (¬ p227) ∨ (¬ p304) ∨ (¬ p367) ∨ (¬ p382) ∨ (¬ p427) ∨ (¬ p633) ∨ p1160 ∨ (¬ p1292) ∨ (¬ p1442) ∨ (¬ p1508)) : (¬ p161) ∨ (¬ p227) ∨ (¬ p304) ∨ (¬ p367) ∨ (¬ p382) ∨ (¬ p633) ∨ (¬ p1292) ∨ (¬ p1442) ∨ (¬ p1508) := by
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
  have u2 : p304 := by
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
  have u5 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1292 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1442 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p427 := by
    exact h2334
  have u11 : (¬ p1160) := by
    exact h16265
  rcases h14602 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u5)
  · exact False.elim (u11 q8)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step19232 (p3 p7 p70 p85 p533 p534 p1249 p1489 : Prop)
    (h16152 : (¬ p7))
    (h14603 : (¬ p3) ∨ p7 ∨ (¬ p70) ∨ (¬ p85) ∨ (¬ p533) ∨ (¬ p534) ∨ (¬ p1249) ∨ (¬ p1489)) : (¬ p3) ∨ (¬ p70) ∨ (¬ p85) ∨ (¬ p533) ∨ (¬ p534) ∨ (¬ p1249) ∨ (¬ p1489) := by
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
  have u3 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14603 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19233 (p7 p45 p790 p802 p1273 p1349 : Prop)
    (h16152 : (¬ p7))
    (h14604 : p7 ∨ (¬ p45) ∨ (¬ p790) ∨ (¬ p802) ∨ (¬ p1273) ∨ (¬ p1349)) : (¬ p45) ∨ (¬ p790) ∨ (¬ p802) ∨ (¬ p1273) ∨ (¬ p1349) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p802 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14604 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19235 (p7 p790 p802 p1226 p1250 p1347 p1508 : Prop)
    (h16152 : (¬ p7))
    (h14606 : p7 ∨ (¬ p790) ∨ (¬ p802) ∨ (¬ p1226) ∨ (¬ p1250) ∨ (¬ p1347) ∨ (¬ p1508)) : (¬ p790) ∨ (¬ p802) ∨ (¬ p1226) ∨ (¬ p1250) ∨ (¬ p1347) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p802 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1250 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14606 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19236 (p7 p25 p44 p261 p304 p633 p790 p802 : Prop)
    (h16152 : (¬ p7))
    (h14607 : p7 ∨ (¬ p25) ∨ (¬ p44) ∨ (¬ p261) ∨ (¬ p304) ∨ (¬ p633) ∨ (¬ p790) ∨ (¬ p802)) : (¬ p25) ∨ (¬ p44) ∨ (¬ p261) ∨ (¬ p304) ∨ (¬ p633) ∨ (¬ p790) ∨ (¬ p802) := by
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
  have u2 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p802 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14607 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19237 (p3 p7 p12 p70 p83 p814 p1124 p1249 p1393 : Prop)
    (h16152 : (¬ p7))
    (h14608 : (¬ p3) ∨ p7 ∨ (¬ p12) ∨ (¬ p70) ∨ (¬ p83) ∨ (¬ p814) ∨ (¬ p1124) ∨ (¬ p1249) ∨ (¬ p1393)) : (¬ p3) ∨ (¬ p12) ∨ (¬ p70) ∨ (¬ p83) ∨ (¬ p814) ∨ (¬ p1124) ∨ (¬ p1249) ∨ (¬ p1393) := by
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
  have u2 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1124 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14608 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19238 (p7 p102 p127 p190 p665 p814 p858 p1077 : Prop)
    (h16152 : (¬ p7))
    (h14609 : p7 ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p190) ∨ (¬ p665) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1077)) : (¬ p102) ∨ (¬ p127) ∨ (¬ p190) ∨ (¬ p665) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1077) := by
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
  have u2 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p665 := by
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
  have u6 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14609 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19239 (p7 p102 p127 p190 p344 p382 p789 p815 p842 : Prop)
    (h16152 : (¬ p7))
    (h14610 : p7 ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p190) ∨ (¬ p344) ∨ (¬ p382) ∨ (¬ p789) ∨ (¬ p815) ∨ (¬ p842)) : (¬ p102) ∨ (¬ p127) ∨ (¬ p190) ∨ (¬ p344) ∨ (¬ p382) ∨ (¬ p789) ∨ (¬ p815) ∨ (¬ p842) := by
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
  have u2 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p789 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14610 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19240 (p7 p88 p533 p577 p633 p756 p814 p858 p1325 : Prop)
    (h16152 : (¬ p7))
    (h14611 : p7 ∨ (¬ p88) ∨ (¬ p533) ∨ (¬ p577) ∨ (¬ p633) ∨ (¬ p756) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1325)) : (¬ p88) ∨ (¬ p533) ∨ (¬ p577) ∨ (¬ p633) ∨ (¬ p756) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p577 := by
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
  rcases h14611 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19242 (p3 p7 p12 p41 p187 p230 p983 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h8348 : p1386)
    (h14614 : (¬ p3) ∨ p7 ∨ (¬ p12) ∨ (¬ p41) ∨ (¬ p187) ∨ p230 ∨ (¬ p983) ∨ (¬ p1386)) : (¬ p3) ∨ (¬ p12) ∨ (¬ p41) ∨ (¬ p187) ∨ (¬ p983) := by
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
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p1386 := by
    exact h8348
  rcases h14614 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step19243 (p7 p135 p163 p188 p226 p256 : Prop)
    (h16152 : (¬ p7))
    (h14615 : p7 ∨ (¬ p135) ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p256)) : (¬ p135) ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p135 := by
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
  have u4 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14615 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19244 (p7 p230 p351 p382 p387 p537 p544 p928 p940 p1709 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h10799 : p1709)
    (h14616 : p7 ∨ p230 ∨ (¬ p351) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p537) ∨ (¬ p544) ∨ (¬ p928) ∨ (¬ p940) ∨ (¬ p1709)) : (¬ p351) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p537) ∨ (¬ p544) ∨ (¬ p928) ∨ (¬ p940) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p230) := by
    exact h16165
  have u9 : p1709 := by
    exact h10799
  rcases h14616 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u9)

theorem step19245 (p3 p7 p70 p351 p387 p544 p616 p1287 : Prop)
    (h16152 : (¬ p7))
    (h14617 : (¬ p3) ∨ p7 ∨ (¬ p70) ∨ (¬ p351) ∨ (¬ p387) ∨ (¬ p544) ∨ (¬ p616) ∨ (¬ p1287)) : (¬ p3) ∨ (¬ p70) ∨ (¬ p351) ∨ (¬ p387) ∨ (¬ p544) ∨ (¬ p616) ∨ (¬ p1287) := by
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
  have u2 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p544 := by
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
  rcases h14617 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19246 (p3 p7 p12 p41 p187 p230 p494 p532 p665 p961 p1184 p1333 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h7053 : p1184)
    (h14618 : (¬ p3) ∨ p7 ∨ (¬ p12) ∨ (¬ p41) ∨ (¬ p187) ∨ p230 ∨ (¬ p494) ∨ (¬ p532) ∨ (¬ p665) ∨ (¬ p961) ∨ (¬ p1184) ∨ (¬ p1333)) : (¬ p3) ∨ (¬ p12) ∨ (¬ p41) ∨ (¬ p187) ∨ (¬ p494) ∨ (¬ p532) ∨ (¬ p665) ∨ (¬ p961) ∨ (¬ p1333) := by
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
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p230) := by
    exact h16165
  have u11 : p1184 := by
    exact h7053
  rcases h14618 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u0)
  · exact False.elim (u9 q1)
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

theorem step19248 (p7 p455 p636 p686 p980 p1139 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h6761 : p1139)
    (h14620 : p7 ∨ (¬ p455) ∨ (¬ p636) ∨ p686 ∨ (¬ p980) ∨ (¬ p1139) ∨ (¬ p1452)) : (¬ p455) ∨ (¬ p636) ∨ (¬ p980) ∨ (¬ p1452) := by
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
  have u5 : (¬ p686) := by
    exact h16205
  have u6 : p1139 := by
    exact h6761
  rcases h14620 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step19249 (p7 p13 p70 p456 p495 p980 p1035 p1140 : Prop)
    (h16152 : (¬ p7))
    (h14621 : p7 ∨ (¬ p13) ∨ (¬ p70) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p980) ∨ (¬ p1035) ∨ (¬ p1140)) : (¬ p13) ∨ (¬ p70) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p980) ∨ (¬ p1035) ∨ (¬ p1140) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p70 := by
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
  have u4 : p980 := by
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
  rcases h14621 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19250 (p7 p17 p258 p350 p518 p790 : Prop)
    (h16152 : (¬ p7))
    (h14622 : p7 ∨ (¬ p17) ∨ (¬ p258) ∨ (¬ p350) ∨ (¬ p518) ∨ (¬ p790)) : (¬ p17) ∨ (¬ p258) ∨ (¬ p350) ∨ (¬ p518) ∨ (¬ p790) := by
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
  have u2 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p518 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14622 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19251 (p7 p41 p126 p189 p230 p256 p427 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h2334 : p427)
    (h14623 : p7 ∨ (¬ p41) ∨ (¬ p126) ∨ (¬ p189) ∨ p230 ∨ (¬ p256) ∨ (¬ p427)) : (¬ p41) ∨ (¬ p126) ∨ (¬ p189) ∨ (¬ p256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
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
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p427 := by
    exact h2334
  rcases h14623 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19252 (p7 p17 p350 p518 p579 p636 p790 : Prop)
    (h16152 : (¬ p7))
    (h14624 : p7 ∨ (¬ p17) ∨ (¬ p350) ∨ (¬ p518) ∨ (¬ p579) ∨ (¬ p636) ∨ (¬ p790)) : (¬ p17) ∨ (¬ p350) ∨ (¬ p518) ∨ (¬ p579) ∨ (¬ p636) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p518 := by
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
  have u5 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14624 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19253 (p7 p12 p45 p84 p129 p169 p237 p983 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h8348 : p1386)
    (h14626 : p7 ∨ (¬ p12) ∨ (¬ p45) ∨ (¬ p84) ∨ p129 ∨ (¬ p169) ∨ (¬ p237) ∨ (¬ p983) ∨ (¬ p1386)) : (¬ p12) ∨ (¬ p45) ∨ (¬ p84) ∨ (¬ p169) ∨ (¬ p237) ∨ (¬ p983) := by
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
  have u2 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p169 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p129) := by
    exact h16154
  have u8 : p1386 := by
    exact h8348
  rcases h14626 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u8)

theorem step19254 (p7 p45 p129 p980 p1139 p1273 p1508 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h6761 : p1139)
    (h14627 : p7 ∨ (¬ p45) ∨ p129 ∨ (¬ p980) ∨ (¬ p1139) ∨ (¬ p1273) ∨ (¬ p1508)) : (¬ p45) ∨ (¬ p980) ∨ (¬ p1273) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p980 := by
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
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p1139 := by
    exact h6761
  rcases h14627 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19255 (p7 p350 p495 p595 p596 p636 : Prop)
    (h16152 : (¬ p7))
    (h14628 : p7 ∨ (¬ p350) ∨ (¬ p495) ∨ (¬ p595) ∨ (¬ p596) ∨ (¬ p636)) : (¬ p350) ∨ (¬ p495) ∨ (¬ p595) ∨ (¬ p596) ∨ (¬ p636) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p596 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14628 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19256 (p7 p126 p127 p129 p143 p163 p226 p420 p495 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h7053 : p1184)
    (h14629 : p7 ∨ (¬ p126) ∨ (¬ p127) ∨ p129 ∨ (¬ p143) ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p1184)) : (¬ p126) ∨ (¬ p127) ∨ (¬ p143) ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p420) ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p129) := by
    exact h16154
  have u9 : p1184 := by
    exact h7053
  rcases h14629 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19258 (p7 p14 p40 p226 p327 p387 p481 p616 p1184 p1287 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h7053 : p1184)
    (h14631 : p7 ∨ (¬ p14) ∨ p40 ∨ (¬ p226) ∨ (¬ p327) ∨ (¬ p387) ∨ (¬ p481) ∨ (¬ p616) ∨ (¬ p1184) ∨ (¬ p1287)) : (¬ p14) ∨ (¬ p226) ∨ (¬ p327) ∨ (¬ p387) ∨ (¬ p481) ∨ (¬ p616) ∨ (¬ p1287) := by
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
  have u2 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p387 := by
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
  rcases h14631 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u8 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u9)
  · exact False.elim (q9 u6)

theorem step19259 (p7 p258 p279 p576 p686 p814 p1393 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16205 : (¬ p686))
    (h14632 : p7 ∨ (¬ p258) ∨ (¬ p279) ∨ (¬ p576) ∨ p686 ∨ (¬ p814) ∨ (¬ p1393)) : (¬ p258) ∨ (¬ p576) ∨ (¬ p814) ∨ (¬ p1393) := by
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
  have u5 : p279 := by
    exact h1444
  have u6 : (¬ p686) := by
    exact h16205
  rcases h14632 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19260 (p7 p17 p87 p258 p580 p633 : Prop)
    (h16152 : (¬ p7))
    (h14633 : p7 ∨ (¬ p17) ∨ (¬ p87) ∨ (¬ p258) ∨ (¬ p580) ∨ (¬ p633)) : (¬ p17) ∨ (¬ p87) ∨ (¬ p258) ∨ (¬ p580) ∨ (¬ p633) := by
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
  have u2 : p258 := by
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
  rcases h14633 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19261 (p7 p14 p40 p127 p226 p323 p427 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h2334 : p427)
    (h14634 : p7 ∨ (¬ p14) ∨ p40 ∨ (¬ p127) ∨ (¬ p226) ∨ (¬ p323) ∨ (¬ p427)) : (¬ p14) ∨ (¬ p127) ∨ (¬ p226) ∨ (¬ p323) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p40) := by
    exact h16150
  have u6 : p427 := by
    exact h2334
  rcases h14634 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19262 (p7 p303 p420 p495 p1184 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h7053 : p1184)
    (h16309 : (¬ p1324))
    (h14635 : p7 ∨ (¬ p303) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p1184) ∨ p1324 ∨ (¬ p1325)) : (¬ p303) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p1325) := by
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
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p1184 := by
    exact h7053
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h14635 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step19263 (p3 p7 p12 p70 p161 p665 p1232 p1333 : Prop)
    (h16152 : (¬ p7))
    (h14636 : (¬ p3) ∨ p7 ∨ (¬ p12) ∨ (¬ p70) ∨ (¬ p161) ∨ (¬ p665) ∨ (¬ p1232) ∨ (¬ p1333)) : (¬ p3) ∨ (¬ p12) ∨ (¬ p70) ∨ (¬ p161) ∨ (¬ p665) ∨ (¬ p1232) ∨ (¬ p1333) := by
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
  have u2 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p665 := by
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
  rcases h14636 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19264 (p3 p7 p12 p39 p63 p68 p616 p665 p858 p1388 : Prop)
    (h16152 : (¬ p7))
    (h14637 : (¬ p3) ∨ p7 ∨ (¬ p12) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p616) ∨ (¬ p665) ∨ (¬ p858) ∨ (¬ p1388)) : (¬ p3) ∨ (¬ p12) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p616) ∨ (¬ p665) ∨ (¬ p858) ∨ (¬ p1388) := by
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
  have u5 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1388 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14637 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19265 (p3 p7 p12 p17 p45 p70 p83 p129 p581 p983 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h8348 : p1386)
    (h14638 : (¬ p3) ∨ p7 ∨ (¬ p12) ∨ (¬ p17) ∨ (¬ p45) ∨ (¬ p70) ∨ (¬ p83) ∨ p129 ∨ (¬ p581) ∨ (¬ p983) ∨ (¬ p1386)) : (¬ p3) ∨ (¬ p12) ∨ (¬ p17) ∨ (¬ p45) ∨ (¬ p70) ∨ (¬ p83) ∨ (¬ p581) ∨ (¬ p983) := by
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
  have u3 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p129) := by
    exact h16154
  have u10 : p1386 := by
    exact h8348
  rcases h14638 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19266 (p7 p17 p45 p129 p279 p303 p420 p579 p1022 p1334 p1393 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h1444 : p279)
    (h14640 : p7 ∨ (¬ p17) ∨ (¬ p45) ∨ p129 ∨ (¬ p279) ∨ (¬ p303) ∨ (¬ p420) ∨ (¬ p579) ∨ (¬ p1022) ∨ (¬ p1334) ∨ (¬ p1393)) : (¬ p17) ∨ (¬ p45) ∨ (¬ p303) ∨ (¬ p420) ∨ (¬ p579) ∨ (¬ p1022) ∨ (¬ p1334) ∨ (¬ p1393) := by
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
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1022 := by
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
  have u9 : (¬ p129) := by
    exact h16154
  have u10 : p279 := by
    exact h1444
  rcases h14640 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u9 q3)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step19267 (p7 p14 p17 p40 p83 p226 p420 p438 p579 p1184 p1370 p1805 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h7053 : p1184)
    (h14641 : p7 ∨ (¬ p14) ∨ (¬ p17) ∨ p40 ∨ (¬ p83) ∨ (¬ p226) ∨ (¬ p420) ∨ (¬ p438) ∨ (¬ p579) ∨ (¬ p1184) ∨ (¬ p1370) ∨ (¬ p1805)) : (¬ p14) ∨ (¬ p17) ∨ (¬ p83) ∨ (¬ p226) ∨ (¬ p420) ∨ (¬ p438) ∨ (¬ p579) ∨ (¬ p1370) ∨ (¬ p1805) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
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
  have u3 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1370 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1805 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p40) := by
    exact h16150
  have u11 : p1184 := by
    exact h7053
  rcases h14641 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
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

theorem step19268 (p7 p45 p127 p129 p788 p1718 p1771 p1798 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h5066 : p788)
    (h14642 : p7 ∨ (¬ p45) ∨ (¬ p127) ∨ p129 ∨ (¬ p788) ∨ (¬ p1718) ∨ (¬ p1771) ∨ (¬ p1798)) : (¬ p45) ∨ (¬ p127) ∨ (¬ p1718) ∨ (¬ p1771) ∨ (¬ p1798) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1718 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1771 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1798 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p788 := by
    exact h5066
  rcases h14642 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step19269 (p7 p83 p302 p1184 p1273 p1333 p1349 p1510 p1772 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h7053 : p1184)
    (h14643 : p7 ∨ (¬ p83) ∨ p302 ∨ (¬ p1184) ∨ (¬ p1273) ∨ (¬ p1333) ∨ (¬ p1349) ∨ (¬ p1510) ∨ (¬ p1772)) : (¬ p83) ∨ (¬ p1273) ∨ (¬ p1333) ∨ (¬ p1349) ∨ (¬ p1510) ∨ (¬ p1772) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1510 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1772 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p302) := by
    exact h16285
  have u8 : p1184 := by
    exact h7053
  rcases h14643 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step19270 (p7 p14 p40 p83 p226 p814 p1140 p1184 p1249 p1258 p1393 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h7053 : p1184)
    (h14644 : p7 ∨ (¬ p14) ∨ p40 ∨ (¬ p83) ∨ (¬ p226) ∨ (¬ p814) ∨ (¬ p1140) ∨ (¬ p1184) ∨ (¬ p1249) ∨ (¬ p1258) ∨ (¬ p1393)) : (¬ p14) ∨ (¬ p83) ∨ (¬ p226) ∨ (¬ p814) ∨ (¬ p1140) ∨ (¬ p1249) ∨ (¬ p1258) ∨ (¬ p1393) := by
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
  have u2 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p40) := by
    exact h16150
  have u10 : p1184 := by
    exact h7053
  rcases h14644 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19271 (p7 p127 p788 p1159 p1444 p1465 p1508 : Prop)
    (h16152 : (¬ p7))
    (h5066 : p788)
    (h16406 : (¬ p1444))
    (h14645 : p7 ∨ (¬ p127) ∨ (¬ p788) ∨ (¬ p1159) ∨ p1444 ∨ (¬ p1465) ∨ (¬ p1508)) : (¬ p127) ∨ (¬ p1159) ∨ (¬ p1465) ∨ (¬ p1508) := by
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
  have u2 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p788 := by
    exact h5066
  have u6 : (¬ p1444) := by
    exact h16406
  rcases h14645 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19272 (p7 p40 p83 p423 p814 p980 p1035 p1124 p1184 p1249 p1393 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h7053 : p1184)
    (h14646 : p7 ∨ p40 ∨ (¬ p83) ∨ (¬ p423) ∨ (¬ p814) ∨ (¬ p980) ∨ (¬ p1035) ∨ (¬ p1124) ∨ (¬ p1184) ∨ (¬ p1249) ∨ (¬ p1393)) : (¬ p83) ∨ (¬ p423) ∨ (¬ p814) ∨ (¬ p980) ∨ (¬ p1035) ∨ (¬ p1124) ∨ (¬ p1249) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1124 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p40) := by
    exact h16150
  have u10 : p1184 := by
    exact h7053
  rcases h14646 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19273 (p7 p17 p83 p420 p438 p579 p983 p1061 p1100 p1335 : Prop)
    (h16152 : (¬ p7))
    (h14647 : p7 ∨ (¬ p17) ∨ (¬ p83) ∨ (¬ p420) ∨ (¬ p438) ∨ (¬ p579) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1100) ∨ (¬ p1335)) : (¬ p17) ∨ (¬ p83) ∨ (¬ p420) ∨ (¬ p438) ∨ (¬ p579) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1100) ∨ (¬ p1335) := by
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
  have u2 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p579 := by
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
  have u7 : p1100 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14647 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19274 (p7 p85 p349 p387 p686 p858 p1184 p1385 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h7053 : p1184)
    (h14648 : p7 ∨ (¬ p85) ∨ (¬ p349) ∨ (¬ p387) ∨ p686 ∨ (¬ p858) ∨ (¬ p1184) ∨ (¬ p1385)) : (¬ p85) ∨ (¬ p349) ∨ (¬ p387) ∨ (¬ p858) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
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
  have u3 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p686) := by
    exact h16205
  have u7 : p1184 := by
    exact h7053
  rcases h14648 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step19275 (p7 p17 p83 p302 p581 p858 p1184 p1385 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h7053 : p1184)
    (h14649 : p7 ∨ (¬ p17) ∨ (¬ p83) ∨ p302 ∨ (¬ p581) ∨ (¬ p858) ∨ (¬ p1184) ∨ (¬ p1385)) : (¬ p17) ∨ (¬ p83) ∨ (¬ p581) ∨ (¬ p858) ∨ (¬ p1385) := by
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
  have u3 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p302) := by
    exact h16285
  have u7 : p1184 := by
    exact h7053
  rcases h14649 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step19276 (p7 p85 p301 p302 p303 p576 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h7053 : p1184)
    (h14650 : p7 ∨ (¬ p85) ∨ (¬ p301) ∨ p302 ∨ (¬ p303) ∨ (¬ p576) ∨ (¬ p1184)) : (¬ p85) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p576) := by
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
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p302) := by
    exact h16285
  have u6 : p1184 := by
    exact h7053
  rcases h14650 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19277 (p7 p67 p423 p1035 p1163 p1226 : Prop)
    (h16152 : (¬ p7))
    (h14651 : p7 ∨ (¬ p67) ∨ (¬ p423) ∨ (¬ p1035) ∨ (¬ p1163) ∨ (¬ p1226)) : (¬ p67) ∨ (¬ p423) ∨ (¬ p1035) ∨ (¬ p1163) ∨ (¬ p1226) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p67 := by
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
  have u3 : p1163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14651 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19278 (p7 p129 p161 p163 p226 p1140 p1184 p1232 p1258 p1508 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h7053 : p1184)
    (h14652 : p7 ∨ p129 ∨ (¬ p161) ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p1140) ∨ (¬ p1184) ∨ (¬ p1232) ∨ (¬ p1258) ∨ (¬ p1508)) : (¬ p161) ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p1140) ∨ (¬ p1232) ∨ (¬ p1258) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p161 := by
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
  have u3 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p129) := by
    exact h16154
  have u9 : p1184 := by
    exact h7053
  rcases h14652 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19279 (p7 p41 p87 p163 p188 p226 : Prop)
    (h16152 : (¬ p7))
    (h14653 : p7 ∨ (¬ p41) ∨ (¬ p87) ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p226)) : (¬ p41) ∨ (¬ p87) ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p226) := by
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
  have u2 : p163 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14653 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19280 (p7 p63 p258 p519 p616 p686 p789 p792 p1287 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h4535 : p792)
    (h14654 : p7 ∨ (¬ p63) ∨ (¬ p258) ∨ (¬ p519) ∨ (¬ p616) ∨ p686 ∨ (¬ p789) ∨ (¬ p792) ∨ (¬ p1287)) : (¬ p63) ∨ (¬ p258) ∨ (¬ p519) ∨ (¬ p616) ∨ (¬ p789) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p519 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p686) := by
    exact h16205
  have u8 : p792 := by
    exact h4535
  rcases h14654 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u7 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u5)

theorem step19281 (p7 p11 p85 p532 p576 p1184 p1324 : Prop)
    (h16152 : (¬ p7))
    (h7053 : p1184)
    (h16309 : (¬ p1324))
    (h14655 : p7 ∨ (¬ p11) ∨ (¬ p85) ∨ (¬ p532) ∨ (¬ p576) ∨ (¬ p1184) ∨ p1324) : (¬ p11) ∨ (¬ p85) ∨ (¬ p532) ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p85 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p1184 := by
    exact h7053
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h14655 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)

theorem step19282 (p7 p17 p129 p163 p226 p279 p481 p581 p803 p1385 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h1444 : p279)
    (h14656 : p7 ∨ (¬ p17) ∨ p129 ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p279) ∨ (¬ p481) ∨ (¬ p581) ∨ (¬ p803) ∨ (¬ p1385)) : (¬ p17) ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p481) ∨ (¬ p581) ∨ (¬ p803) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
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
  have u3 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p803 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p129) := by
    exact h16154
  have u9 : p279 := by
    exact h1444
  rcases h14656 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19283 (p7 p126 p258 p420 p495 p686 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h7053 : p1184)
    (h14657 : p7 ∨ (¬ p126) ∨ (¬ p258) ∨ (¬ p420) ∨ (¬ p495) ∨ p686 ∨ (¬ p1184)) : (¬ p126) ∨ (¬ p258) ∨ (¬ p420) ∨ (¬ p495) := by
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
  have u2 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p686) := by
    exact h16205
  have u6 : p1184 := by
    exact h7053
  rcases h14657 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step19284 (p7 p70 p351 p420 p495 p544 p561 p1036 p1061 : Prop)
    (h16152 : (¬ p7))
    (h14658 : p7 ∨ (¬ p70) ∨ (¬ p351) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p544) ∨ (¬ p561) ∨ (¬ p1036) ∨ (¬ p1061)) : (¬ p70) ∨ (¬ p351) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p544) ∨ (¬ p561) ∨ (¬ p1036) ∨ (¬ p1061) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
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
  have u6 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14658 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19285 (p7 p401 p544 p789 p842 p1036 p1060 : Prop)
    (h16152 : (¬ p7))
    (h14659 : p7 ∨ (¬ p401) ∨ (¬ p544) ∨ (¬ p789) ∨ (¬ p842) ∨ (¬ p1036) ∨ (¬ p1060)) : (¬ p401) ∨ (¬ p544) ∨ (¬ p789) ∨ (¬ p842) ∨ (¬ p1036) ∨ (¬ p1060) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p401 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p842 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1060 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14659 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19286 (p7 p70 p85 p302 p343 p544 p561 p858 p1036 p1061 p1385 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h1950 : p343)
    (h14660 : p7 ∨ (¬ p70) ∨ (¬ p85) ∨ p302 ∨ (¬ p343) ∨ (¬ p544) ∨ (¬ p561) ∨ (¬ p858) ∨ (¬ p1036) ∨ (¬ p1061) ∨ (¬ p1385)) : (¬ p70) ∨ (¬ p85) ∨ (¬ p544) ∨ (¬ p561) ∨ (¬ p858) ∨ (¬ p1036) ∨ (¬ p1061) ∨ (¬ p1385) := by
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
  have u2 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p858 := by
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
  have u7 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p302) := by
    exact h16285
  have u10 : p343 := by
    exact h1950
  rcases h14660 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u9 q3)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step19287 (p7 p39 p63 p68 p106 p495 p561 p636 p1036 p1061 : Prop)
    (h16152 : (¬ p7))
    (h14661 : p7 ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p106) ∨ (¬ p495) ∨ (¬ p561) ∨ (¬ p636) ∨ (¬ p1036) ∨ (¬ p1061)) : (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p106) ∨ (¬ p495) ∨ (¬ p561) ∨ (¬ p636) ∨ (¬ p1036) ∨ (¬ p1061) := by
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
  have u3 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p561 := by
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
  have u8 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14661 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19288 (p7 p45 p129 p132 p185 p256 p928 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h786 : p132)
    (h14662 : p7 ∨ (¬ p45) ∨ p129 ∨ (¬ p132) ∨ (¬ p185) ∨ (¬ p256) ∨ (¬ p928)) : (¬ p45) ∨ (¬ p185) ∨ (¬ p256) ∨ (¬ p928) := by
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
  have u2 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p132 := by
    exact h786
  rcases h14662 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19289 (p7 p8 p41 p132 p187 p230 p256 p561 p728 p814 p858 p1334 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16165 : (¬ p230))
    (h14663 : p7 ∨ (¬ p8) ∨ (¬ p41) ∨ (¬ p132) ∨ (¬ p187) ∨ p230 ∨ (¬ p256) ∨ (¬ p561) ∨ (¬ p728) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1334)) : (¬ p8) ∨ (¬ p41) ∨ (¬ p187) ∨ (¬ p256) ∨ (¬ p561) ∨ (¬ p728) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1334) := by
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
  have u2 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p132 := by
    exact h786
  have u11 : (¬ p230) := by
    exact h16165
  rcases h14663 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u2)
  · exact False.elim (u11 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step19290 (p7 p41 p132 p158 p170 p230 p256 p814 p983 p1061 p1335 p1391 p1545 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16165 : (¬ p230))
    (h14664 : p7 ∨ (¬ p41) ∨ (¬ p132) ∨ (¬ p158) ∨ (¬ p170) ∨ p230 ∨ (¬ p256) ∨ (¬ p814) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1335) ∨ (¬ p1391) ∨ (¬ p1545)) : (¬ p41) ∨ (¬ p158) ∨ (¬ p170) ∨ (¬ p256) ∨ (¬ p814) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1335) ∨ (¬ p1391) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p814 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1391 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : p132 := by
    exact h786
  have u12 : (¬ p230) := by
    exact h16165
  rcases h14664 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u12 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)
  · exact False.elim (q12 u9)

theorem step19292 (p7 p106 p980 p1036 p1083 p1452 : Prop)
    (h16152 : (¬ p7))
    (h14666 : p7 ∨ (¬ p106) ∨ (¬ p980) ∨ (¬ p1036) ∨ (¬ p1083) ∨ (¬ p1452)) : (¬ p106) ∨ (¬ p980) ∨ (¬ p1036) ∨ (¬ p1083) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p106 := by
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
  rcases h14666 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19293 (p7 p8 p70 p85 p561 p728 p858 p1334 p1385 : Prop)
    (h16152 : (¬ p7))
    (h14667 : p7 ∨ (¬ p8) ∨ (¬ p70) ∨ (¬ p85) ∨ (¬ p561) ∨ (¬ p728) ∨ (¬ p858) ∨ (¬ p1334) ∨ (¬ p1385)) : (¬ p8) ∨ (¬ p70) ∨ (¬ p85) ∨ (¬ p561) ∨ (¬ p728) ∨ (¬ p858) ∨ (¬ p1334) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
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
  have u3 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p728 := by
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
  rcases h14667 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19295 (p7 p27 p103 p225 p633 p662 p1077 : Prop)
    (h16152 : (¬ p7))
    (h14670 : p7 ∨ (¬ p27) ∨ (¬ p103) ∨ (¬ p225) ∨ (¬ p633) ∨ (¬ p662) ∨ (¬ p1077)) : (¬ p27) ∨ (¬ p103) ∨ (¬ p225) ∨ (¬ p633) ∨ (¬ p662) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p27 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p662 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14670 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19296 (p7 p8 p17 p83 p172 p225 p581 p918 p1100 : Prop)
    (h16152 : (¬ p7))
    (h14671 : p7 ∨ (¬ p8) ∨ (¬ p17) ∨ (¬ p83) ∨ (¬ p172) ∨ (¬ p225) ∨ (¬ p581) ∨ (¬ p918) ∨ (¬ p1100)) : (¬ p8) ∨ (¬ p17) ∨ (¬ p83) ∨ (¬ p172) ∨ (¬ p225) ∨ (¬ p581) ∨ (¬ p918) ∨ (¬ p1100) := by
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
  have u3 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1100 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14671 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19297 (p7 p258 p350 p367 p382 p519 p789 : Prop)
    (h16152 : (¬ p7))
    (h14672 : p7 ∨ (¬ p258) ∨ (¬ p350) ∨ (¬ p367) ∨ (¬ p382) ∨ (¬ p519) ∨ (¬ p789)) : (¬ p258) ∨ (¬ p350) ∨ (¬ p367) ∨ (¬ p382) ∨ (¬ p519) ∨ (¬ p789) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p367 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p519 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14672 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19299 (p7 p8 p101 p346 p788 p1055 p1181 : Prop)
    (h16152 : (¬ p7))
    (h5066 : p788)
    (h16272 : (¬ p1181))
    (h14674 : p7 ∨ (¬ p8) ∨ (¬ p101) ∨ (¬ p346) ∨ (¬ p788) ∨ (¬ p1055) ∨ p1181) : (¬ p8) ∨ (¬ p101) ∨ (¬ p346) ∨ (¬ p1055) := by
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
  have u2 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p788 := by
    exact h5066
  have u6 : (¬ p1181) := by
    exact h16272
  rcases h14674 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step19300 (p7 p8 p106 p225 p1055 p1077 : Prop)
    (h16152 : (¬ p7))
    (h14675 : p7 ∨ (¬ p8) ∨ (¬ p106) ∨ (¬ p225) ∨ (¬ p1055) ∨ (¬ p1077)) : (¬ p8) ∨ (¬ p106) ∨ (¬ p225) ∨ (¬ p1055) ∨ (¬ p1077) := by
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
  rcases h14675 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19302 (p7 p8 p12 p129 p163 p343 p1055 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h1950 : p343)
    (h14677 : p7 ∨ (¬ p8) ∨ (¬ p12) ∨ p129 ∨ (¬ p163) ∨ (¬ p343) ∨ (¬ p1055)) : (¬ p8) ∨ (¬ p12) ∨ (¬ p163) ∨ (¬ p1055) := by
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
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p343 := by
    exact h1950
  rcases h14677 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step19303 (p7 p45 p129 p169 p346 p544 p928 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h6478 : p1075)
    (h14678 : p7 ∨ (¬ p45) ∨ p129 ∨ (¬ p169) ∨ (¬ p346) ∨ (¬ p544) ∨ (¬ p928) ∨ (¬ p1075)) : (¬ p45) ∨ (¬ p169) ∨ (¬ p346) ∨ (¬ p544) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p169 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p1075 := by
    exact h6478
  rcases h14678 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step19305 (p7 p101 p323 p348 p639 p664 p1074 : Prop)
    (h16152 : (¬ p7))
    (h14680 : p7 ∨ (¬ p101) ∨ (¬ p323) ∨ (¬ p348) ∨ (¬ p639) ∨ (¬ p664) ∨ (¬ p1074)) : (¬ p101) ∨ (¬ p323) ∨ (¬ p348) ∨ (¬ p639) ∨ (¬ p664) ∨ (¬ p1074) := by
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
  have u3 : p639 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14680 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19306 (p3 p7 p70 p85 p290 p346 p544 p918 : Prop)
    (h16152 : (¬ p7))
    (h14681 : (¬ p3) ∨ p7 ∨ (¬ p70) ∨ (¬ p85) ∨ (¬ p290) ∨ (¬ p346) ∨ (¬ p544) ∨ (¬ p918)) : (¬ p3) ∨ (¬ p70) ∨ (¬ p85) ∨ (¬ p290) ∨ (¬ p346) ∨ (¬ p544) ∨ (¬ p918) := by
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
  have u3 : p290 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14681 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19308 (p7 p39 p69 p88 p185 p664 p904 p1096 p1115 : Prop)
    (h16152 : (¬ p7))
    (h14683 : p7 ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p185) ∨ (¬ p664) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1115)) : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p185) ∨ (¬ p664) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1115) := by
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
  have u4 : p664 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14683 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19309 (p7 p288 p499 p578 p635 p1099 : Prop)
    (h16152 : (¬ p7))
    (h14684 : p7 ∨ (¬ p288) ∨ (¬ p499) ∨ (¬ p578) ∨ (¬ p635) ∨ (¬ p1099)) : (¬ p288) ∨ (¬ p499) ∨ (¬ p578) ∨ (¬ p635) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p288 := by
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
  have u3 : p635 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14684 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19310 (p7 p344 p456 p633 p664 p1079 : Prop)
    (h16152 : (¬ p7))
    (h14685 : p7 ∨ (¬ p344) ∨ (¬ p456) ∨ (¬ p633) ∨ (¬ p664) ∨ (¬ p1079)) : (¬ p344) ∨ (¬ p456) ∨ (¬ p633) ∨ (¬ p664) ∨ (¬ p1079) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1079 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14685 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19311 (p7 p39 p69 p88 p343 p344 p639 p814 p858 p1096 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16309 : (¬ p1324))
    (h14686 : p7 ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p639) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1096) ∨ p1324 ∨ (¬ p1325)) : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p344) ∨ (¬ p639) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1096) ∨ (¬ p1325) := by
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
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p639 := by
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
  have u7 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p343 := by
    exact h1950
  have u11 : (¬ p1324) := by
    exact h16309
  rcases h14686 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
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
  · exact False.elim (u11 q10)
  · exact False.elim (q11 u8)

theorem step19312 (p7 p16 p185 p344 p499 p633 p664 p1115 : Prop)
    (h16152 : (¬ p7))
    (h14687 : p7 ∨ (¬ p16) ∨ (¬ p185) ∨ (¬ p344) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p664) ∨ (¬ p1115)) : (¬ p16) ∨ (¬ p185) ∨ (¬ p344) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p664) ∨ (¬ p1115) := by
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
  have u6 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14687 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19313 (p7 p40 p69 p343 p344 p499 p633 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h1950 : p343)
    (h14688 : p7 ∨ p40 ∨ (¬ p69) ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p499) ∨ (¬ p633)) : (¬ p69) ∨ (¬ p344) ∨ (¬ p499) ∨ (¬ p633) := by
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
  have u6 : p343 := by
    exact h1950
  rcases h14688 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19314 (p7 p21 p72 p127 p229 p344 p560 p633 p664 p1055 : Prop)
    (h16152 : (¬ p7))
    (h14689 : p7 ∨ (¬ p21) ∨ (¬ p72) ∨ (¬ p127) ∨ (¬ p229) ∨ (¬ p344) ∨ (¬ p560) ∨ (¬ p633) ∨ (¬ p664) ∨ (¬ p1055)) : (¬ p21) ∨ (¬ p72) ∨ (¬ p127) ∨ (¬ p229) ∨ (¬ p344) ∨ (¬ p560) ∨ (¬ p633) ∨ (¬ p664) ∨ (¬ p1055) := by
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
  have u3 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14689 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19315 (p7 p8 p302 p343 p980 p1055 p1333 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h1950 : p343)
    (h14690 : p7 ∨ (¬ p8) ∨ p302 ∨ (¬ p343) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1333)) : (¬ p8) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p302) := by
    exact h16285
  have u6 : p343 := by
    exact h1950
  rcases h14690 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19316 (p7 p287 p578 p636 p1076 p1116 : Prop)
    (h16152 : (¬ p7))
    (h14691 : p7 ∨ (¬ p287) ∨ (¬ p578) ∨ (¬ p636) ∨ (¬ p1076) ∨ (¬ p1116)) : (¬ p287) ∨ (¬ p578) ∨ (¬ p636) ∨ (¬ p1076) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p578 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p636 := by
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
  rcases h14691 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19317 (p3 p7 p16 p19 p71 p143 p229 p261 p288 p304 : Prop)
    (h16152 : (¬ p7))
    (h14692 : (¬ p3) ∨ p7 ∨ (¬ p16) ∨ (¬ p19) ∨ (¬ p71) ∨ (¬ p143) ∨ (¬ p229) ∨ (¬ p261) ∨ (¬ p288) ∨ (¬ p304)) : (¬ p3) ∨ (¬ p16) ∨ (¬ p19) ∨ (¬ p71) ∨ (¬ p143) ∨ (¬ p229) ∨ (¬ p261) ∨ (¬ p288) ∨ (¬ p304) := by
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
  have u2 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14692 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19318 (p3 p7 p70 p85 p544 p664 p918 p1115 : Prop)
    (h16152 : (¬ p7))
    (h14693 : (¬ p3) ∨ p7 ∨ (¬ p70) ∨ (¬ p85) ∨ (¬ p544) ∨ (¬ p664) ∨ (¬ p918) ∨ (¬ p1115)) : (¬ p3) ∨ (¬ p70) ∨ (¬ p85) ∨ (¬ p544) ∨ (¬ p664) ∨ (¬ p918) ∨ (¬ p1115) := by
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
  have u4 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14693 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19319 (p7 p40 p69 p346 p544 p883 p1075 p1096 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h6478 : p1075)
    (h14694 : p7 ∨ p40 ∨ (¬ p69) ∨ (¬ p346) ∨ (¬ p544) ∨ (¬ p883) ∨ (¬ p1075) ∨ (¬ p1096)) : (¬ p69) ∨ (¬ p346) ∨ (¬ p544) ∨ (¬ p883) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
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
  have u3 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p40) := by
    exact h16150
  have u7 : p1075 := by
    exact h6478
  rcases h14694 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step19320 (p7 p15 p19 p108 p346 p544 p1075 p1136 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16259 : (¬ p1136))
    (h14695 : p7 ∨ (¬ p15) ∨ (¬ p19) ∨ (¬ p108) ∨ (¬ p346) ∨ (¬ p544) ∨ (¬ p1075) ∨ p1136) : (¬ p15) ∨ (¬ p19) ∨ (¬ p108) ∨ (¬ p346) ∨ (¬ p544) := by
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
  have u2 : p108 := by
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
  have u6 : p1075 := by
    exact h6478
  have u7 : (¬ p1136) := by
    exact h16259
  rcases h14695 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u6)
  · exact False.elim (u7 q7)

theorem step19321 (p7 p72 p228 p382 p480 p532 p1035 p1140 p1187 : Prop)
    (h16152 : (¬ p7))
    (h14696 : p7 ∨ (¬ p72) ∨ (¬ p228) ∨ (¬ p382) ∨ (¬ p480) ∨ (¬ p532) ∨ (¬ p1035) ∨ (¬ p1140) ∨ (¬ p1187)) : (¬ p72) ∨ (¬ p228) ∨ (¬ p382) ∨ (¬ p480) ∨ (¬ p532) ∨ (¬ p1035) ∨ (¬ p1140) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p228 := by
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
  have u4 : p532 := by
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
  have u7 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14696 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19322 (p7 p170 p238 p790 p802 p1055 p1116 : Prop)
    (h16152 : (¬ p7))
    (h14697 : p7 ∨ (¬ p170) ∨ (¬ p238) ∨ (¬ p790) ∨ (¬ p802) ∨ (¬ p1055) ∨ (¬ p1116)) : (¬ p170) ∨ (¬ p238) ∨ (¬ p790) ∨ (¬ p802) ∨ (¬ p1055) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p802 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14697 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19323 (p7 p14 p15 p304 p500 p544 p664 p1076 : Prop)
    (h16152 : (¬ p7))
    (h14698 : p7 ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p304) ∨ (¬ p500) ∨ (¬ p544) ∨ (¬ p664) ∨ (¬ p1076)) : (¬ p14) ∨ (¬ p15) ∨ (¬ p304) ∨ (¬ p500) ∨ (¬ p544) ∨ (¬ p664) ∨ (¬ p1076) := by
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
  have u2 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14698 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19324 (p7 p135 p169 p189 p237 p258 p544 p664 p1076 : Prop)
    (h16152 : (¬ p7))
    (h14699 : p7 ∨ (¬ p135) ∨ (¬ p169) ∨ (¬ p189) ∨ (¬ p237) ∨ (¬ p258) ∨ (¬ p544) ∨ (¬ p664) ∨ (¬ p1076)) : (¬ p135) ∨ (¬ p169) ∨ (¬ p189) ∨ (¬ p237) ∨ (¬ p258) ∨ (¬ p544) ∨ (¬ p664) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p135 := by
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
  have u3 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14699 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19325 (p7 p45 p84 p169 p237 p302 p303 p343 p434 p544 p690 p802 p819 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h1950 : p343)
    (h14700 : p7 ∨ (¬ p45) ∨ (¬ p84) ∨ (¬ p169) ∨ (¬ p237) ∨ p302 ∨ (¬ p303) ∨ (¬ p343) ∨ (¬ p434) ∨ (¬ p544) ∨ (¬ p690) ∨ (¬ p802) ∨ (¬ p819)) : (¬ p45) ∨ (¬ p84) ∨ (¬ p169) ∨ (¬ p237) ∨ (¬ p303) ∨ (¬ p434) ∨ (¬ p544) ∨ (¬ p690) ∨ (¬ p802) ∨ (¬ p819) := by
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
  have u2 : p169 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p802 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p819 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : (¬ p302) := by
    exact h16285
  have u12 : p343 := by
    exact h1950
  rcases h14700 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u11 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u12)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)
  · exact False.elim (q12 u9)

theorem step19326 (p7 p233 p435 p680 p686 p687 p1055 p1077 : Prop)
    (h16152 : (¬ p7))
    (h2345 : p233)
    (h16205 : (¬ p686))
    (h14701 : p7 ∨ (¬ p233) ∨ (¬ p435) ∨ (¬ p680) ∨ p686 ∨ (¬ p687) ∨ (¬ p1055) ∨ (¬ p1077)) : (¬ p435) ∨ (¬ p680) ∨ (¬ p687) ∨ (¬ p1055) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p687 := by
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
  have u6 : p233 := by
    exact h2345
  have u7 : (¬ p686) := by
    exact h16205
  rcases h14701 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step19327 (p7 p14 p44 p90 p193 p241 p343 p544 p686 p918 p1055 p1077 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16205 : (¬ p686))
    (h14702 : p7 ∨ (¬ p14) ∨ (¬ p44) ∨ (¬ p90) ∨ (¬ p193) ∨ (¬ p241) ∨ (¬ p343) ∨ (¬ p544) ∨ p686 ∨ (¬ p918) ∨ (¬ p1055) ∨ (¬ p1077)) : (¬ p14) ∨ (¬ p44) ∨ (¬ p90) ∨ (¬ p193) ∨ (¬ p241) ∨ (¬ p544) ∨ (¬ p918) ∨ (¬ p1055) ∨ (¬ p1077) := by
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
  have u4 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p918 := by
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
  have u10 : p343 := by
    exact h1950
  have u11 : (¬ p686) := by
    exact h16205
  rcases h14702 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u5)
  · exact False.elim (u11 q8)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step19329 (p7 p63 p169 p351 p434 p544 p621 p690 p928 : Prop)
    (h16152 : (¬ p7))
    (h14704 : p7 ∨ (¬ p63) ∨ (¬ p169) ∨ (¬ p351) ∨ (¬ p434) ∨ (¬ p544) ∨ (¬ p621) ∨ (¬ p690) ∨ (¬ p928)) : (¬ p63) ∨ (¬ p169) ∨ (¬ p351) ∨ (¬ p434) ∨ (¬ p544) ∨ (¬ p621) ∨ (¬ p690) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p169 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p621 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14704 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19330 (p7 p125 p135 p169 p189 p237 p265 p303 p343 p544 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16309 : (¬ p1324))
    (h14705 : p7 ∨ (¬ p125) ∨ (¬ p135) ∨ (¬ p169) ∨ (¬ p189) ∨ (¬ p237) ∨ (¬ p265) ∨ (¬ p303) ∨ (¬ p343) ∨ (¬ p544) ∨ p1324 ∨ (¬ p1325)) : (¬ p125) ∨ (¬ p135) ∨ (¬ p169) ∨ (¬ p189) ∨ (¬ p237) ∨ (¬ p265) ∨ (¬ p303) ∨ (¬ p544) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p169 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p343 := by
    exact h1950
  have u11 : (¬ p1324) := by
    exact h16309
  rcases h14705 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
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
  · exact False.elim (u11 q10)
  · exact False.elim (q11 u8)

theorem step19331 (p3 p7 p41 p87 p185 p187 p544 p664 p1115 : Prop)
    (h16152 : (¬ p7))
    (h14706 : (¬ p3) ∨ p7 ∨ (¬ p41) ∨ (¬ p87) ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p544) ∨ (¬ p664) ∨ (¬ p1115)) : (¬ p3) ∨ (¬ p41) ∨ (¬ p87) ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p544) ∨ (¬ p664) ∨ (¬ p1115) := by
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
  have u2 : p87 := by
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
  have u5 : p544 := by
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
  rcases h14706 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19332 (p3 p7 p135 p185 p187 p256 p544 p664 p1115 : Prop)
    (h16152 : (¬ p7))
    (h14707 : (¬ p3) ∨ p7 ∨ (¬ p135) ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p256) ∨ (¬ p544) ∨ (¬ p664) ∨ (¬ p1115)) : (¬ p3) ∨ (¬ p135) ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p256) ∨ (¬ p544) ∨ (¬ p664) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
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
  have u4 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p544 := by
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
  rcases h14707 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19333 (p7 p16 p17 p258 p664 p904 p1076 p1096 : Prop)
    (h16152 : (¬ p7))
    (h14708 : p7 ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p258) ∨ (¬ p664) ∨ (¬ p904) ∨ (¬ p1076) ∨ (¬ p1096)) : (¬ p16) ∨ (¬ p17) ∨ (¬ p258) ∨ (¬ p664) ∨ (¬ p904) ∨ (¬ p1076) ∨ (¬ p1096) := by
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
  have u3 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14708 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19337 (p7 p8 p17 p45 p129 p158 p258 p279 p664 p928 p1076 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h1444 : p279)
    (h14712 : p7 ∨ (¬ p8) ∨ (¬ p17) ∨ (¬ p45) ∨ p129 ∨ (¬ p158) ∨ (¬ p258) ∨ (¬ p279) ∨ (¬ p664) ∨ (¬ p928) ∨ (¬ p1076)) : (¬ p8) ∨ (¬ p17) ∨ (¬ p45) ∨ (¬ p158) ∨ (¬ p258) ∨ (¬ p664) ∨ (¬ p928) ∨ (¬ p1076) := by
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
  have u2 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p129) := by
    exact h16154
  have u10 : p279 := by
    exact h1444
  rcases h14712 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19338 (p7 p18 p128 p210 p265 p301 p303 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16309 : (¬ p1324))
    (h14713 : p7 ∨ (¬ p18) ∨ (¬ p128) ∨ (¬ p210) ∨ p265 ∨ (¬ p301) ∨ (¬ p303) ∨ p1324 ∨ (¬ p1325)) : (¬ p18) ∨ (¬ p210) ∨ p265 ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p1325) := by
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
  have u2 : (¬ p265) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : p128 := by
    exact h653
  have u8 : (¬ p1324) := by
    exact h16309
  rcases h14713 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u1)
  · exact False.elim (u2 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u8 q7)
  · exact False.elim (q8 u5)

theorem step19339 (p7 p127 p226 p686 p788 p1036 p1077 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h5066 : p788)
    (h14714 : p7 ∨ (¬ p127) ∨ (¬ p226) ∨ p686 ∨ (¬ p788) ∨ (¬ p1036) ∨ (¬ p1077)) : (¬ p127) ∨ (¬ p226) ∨ (¬ p1036) ∨ (¬ p1077) := by
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
  rcases h14714 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19340 (p7 p135 p170 p238 p256 p1055 p1116 : Prop)
    (h16152 : (¬ p7))
    (h14715 : p7 ∨ (¬ p135) ∨ (¬ p170) ∨ (¬ p238) ∨ (¬ p256) ∨ (¬ p1055) ∨ (¬ p1116)) : (¬ p135) ∨ (¬ p170) ∨ (¬ p238) ∨ (¬ p256) ∨ (¬ p1055) ∨ (¬ p1116) := by
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
  have u4 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14715 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19341 (p7 p46 p170 p229 p560 p1055 p1116 : Prop)
    (h16152 : (¬ p7))
    (h14716 : p7 ∨ (¬ p46) ∨ (¬ p170) ∨ (¬ p229) ∨ (¬ p560) ∨ (¬ p1055) ∨ (¬ p1116)) : (¬ p46) ∨ (¬ p170) ∨ (¬ p229) ∨ (¬ p560) ∨ (¬ p1055) ∨ (¬ p1116) := by
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
  have u4 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14716 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19342 (p7 p63 p129 p170 p792 p1074 p1099 p1116 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h4535 : p792)
    (h14717 : p7 ∨ (¬ p63) ∨ p129 ∨ (¬ p170) ∨ (¬ p792) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1116)) : (¬ p63) ∨ (¬ p170) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p792 := by
    exact h4535
  rcases h14717 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step19343 (p7 p17 p39 p69 p88 p301 p302 p303 p343 p544 p883 p1096 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h1950 : p343)
    (h14718 : p7 ∨ (¬ p17) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p301) ∨ p302 ∨ (¬ p303) ∨ (¬ p343) ∨ (¬ p544) ∨ (¬ p883) ∨ (¬ p1096)) : (¬ p17) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p544) ∨ (¬ p883) ∨ (¬ p1096) := by
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
  have u6 : p544 := by
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
  have u10 : (¬ p302) := by
    exact h16285
  have u11 : p343 := by
    exact h1950
  rcases h14718 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u10 q6)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u11)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step19344 (p7 p595 p686 p1074 p1077 p1099 p1664 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h10244 : p1664)
    (h14719 : p7 ∨ (¬ p595) ∨ p686 ∨ (¬ p1074) ∨ (¬ p1077) ∨ (¬ p1099) ∨ (¬ p1664)) : (¬ p595) ∨ (¬ p1074) ∨ (¬ p1077) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p595 := by
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
  have u5 : (¬ p686) := by
    exact h16205
  have u6 : p1664 := by
    exact h10244
  rcases h14719 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19345 (p7 p16 p17 p301 p438 p1225 p1229 p1335 : Prop)
    (h16152 : (¬ p7))
    (h14720 : p7 ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p301) ∨ (¬ p438) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1335)) : (¬ p16) ∨ (¬ p17) ∨ (¬ p301) ∨ (¬ p438) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1335) := by
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
  have u2 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p438 := by
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
  rcases h14720 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19346 (p7 p126 p258 p324 p434 p435 p686 p788 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h5066 : p788)
    (h14721 : p7 ∨ (¬ p126) ∨ (¬ p258) ∨ (¬ p324) ∨ (¬ p434) ∨ (¬ p435) ∨ p686 ∨ (¬ p788)) : (¬ p126) ∨ (¬ p258) ∨ (¬ p324) ∨ (¬ p434) ∨ (¬ p435) := by
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
  have u2 : p324 := by
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
  have u6 : (¬ p686) := by
    exact h16205
  have u7 : p788 := by
    exact h5066
  rcases h14721 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u7)

theorem step19347 (p7 p17 p279 p581 p918 p1115 p1181 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16272 : (¬ p1181))
    (h14722 : p7 ∨ (¬ p17) ∨ (¬ p279) ∨ (¬ p581) ∨ (¬ p918) ∨ (¬ p1115) ∨ p1181) : (¬ p17) ∨ (¬ p581) ∨ (¬ p918) ∨ (¬ p1115) := by
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
  have u2 : p918 := by
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
  have u6 : (¬ p1181) := by
    exact h16272
  rcases h14722 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step19348 (p3 p7 p41 p87 p106 p185 p187 p1077 p1115 : Prop)
    (h16152 : (¬ p7))
    (h14723 : (¬ p3) ∨ p7 ∨ (¬ p41) ∨ (¬ p87) ∨ (¬ p106) ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p1077) ∨ (¬ p1115)) : (¬ p3) ∨ (¬ p41) ∨ (¬ p87) ∨ (¬ p106) ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p1077) ∨ (¬ p1115) := by
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
  have u2 : p87 := by
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
  have u5 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14723 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19349 (p7 p132 p256 p280 p387 p814 p858 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16173 : (¬ p280))
    (h14724 : p7 ∨ (¬ p132) ∨ (¬ p256) ∨ p280 ∨ (¬ p387) ∨ (¬ p814) ∨ (¬ p858)) : (¬ p256) ∨ (¬ p387) ∨ (¬ p814) ∨ (¬ p858) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p387 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p132 := by
    exact h786
  have u6 : (¬ p280) := by
    exact h16173
  rcases h14724 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19350 (p7 p101 p121 p308 p1055 p1082 : Prop)
    (h16152 : (¬ p7))
    (h14726 : p7 ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p308) ∨ (¬ p1055) ∨ (¬ p1082)) : (¬ p101) ∨ (¬ p121) ∨ (¬ p308) ∨ (¬ p1055) ∨ (¬ p1082) := by
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
  have u2 : p308 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1082 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14726 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19351 (p7 p135 p160 p185 p256 p1040 p1115 p1250 p1348 p1465 : Prop)
    (h16152 : (¬ p7))
    (h14727 : p7 ∨ (¬ p135) ∨ (¬ p160) ∨ (¬ p185) ∨ (¬ p256) ∨ (¬ p1040) ∨ (¬ p1115) ∨ (¬ p1250) ∨ (¬ p1348) ∨ (¬ p1465)) : (¬ p135) ∨ (¬ p160) ∨ (¬ p185) ∨ (¬ p256) ∨ (¬ p1040) ∨ (¬ p1115) ∨ (¬ p1250) ∨ (¬ p1348) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p256 := by
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
  have u6 : p1250 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14727 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19352 (p7 p90 p237 p840 p897 p922 : Prop)
    (h16152 : (¬ p7))
    (h14728 : p7 ∨ (¬ p90) ∨ (¬ p237) ∨ (¬ p840) ∨ (¬ p897) ∨ (¬ p922)) : (¬ p90) ∨ (¬ p237) ∨ (¬ p840) ∨ (¬ p897) ∨ (¬ p922) := by
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
  have u2 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p922 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14728 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19354 (p7 p8 p89 p164 p193 p225 p306 p1040 p1076 p1136 p1250 p1465 p1508 : Prop)
    (h16152 : (¬ p7))
    (h789 : p164)
    (h16259 : (¬ p1136))
    (h14731 : p7 ∨ (¬ p8) ∨ (¬ p89) ∨ (¬ p164) ∨ (¬ p193) ∨ (¬ p225) ∨ (¬ p306) ∨ (¬ p1040) ∨ (¬ p1076) ∨ p1136 ∨ (¬ p1250) ∨ (¬ p1465) ∨ (¬ p1508)) : (¬ p8) ∨ (¬ p89) ∨ (¬ p193) ∨ (¬ p225) ∨ (¬ p306) ∨ (¬ p1040) ∨ (¬ p1076) ∨ (¬ p1250) ∨ (¬ p1465) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
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
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p306 := by
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
  have u7 : p1250 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : p164 := by
    exact h789
  have u12 : (¬ p1136) := by
    exact h16259
  rcases h14731 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (u12 q9)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)
  · exact False.elim (q12 u9)

theorem step19355 (p7 p45 p129 p164 p225 p840 p928 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h789 : p164)
    (h14734 : p7 ∨ (¬ p45) ∨ p129 ∨ (¬ p164) ∨ (¬ p225) ∨ (¬ p840) ∨ (¬ p928)) : (¬ p45) ∨ (¬ p225) ∨ (¬ p840) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p225 := by
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
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p164 := by
    exact h789
  rcases h14734 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19356 (p7 p8 p225 p561 p1039 p1159 : Prop)
    (h16152 : (¬ p7))
    (h14735 : p7 ∨ (¬ p8) ∨ (¬ p225) ∨ (¬ p561) ∨ (¬ p1039) ∨ (¬ p1159)) : (¬ p8) ∨ (¬ p225) ∨ (¬ p561) ∨ (¬ p1039) ∨ (¬ p1159) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1039 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14735 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19357 (p7 p39 p63 p68 p616 p1035 p1140 p1335 p1545 : Prop)
    (h16152 : (¬ p7))
    (h14736 : p7 ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p616) ∨ (¬ p1035) ∨ (¬ p1140) ∨ (¬ p1335) ∨ (¬ p1545)) : (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p616) ∨ (¬ p1035) ∨ (¬ p1140) ∨ (¬ p1335) ∨ (¬ p1545) := by
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
  have u3 : p616 := by
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
  have u6 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14736 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19359 (p7 p103 p124 p213 p225 p344 : Prop)
    (h16152 : (¬ p7))
    (h14738 : p7 ∨ (¬ p103) ∨ (¬ p124) ∨ (¬ p213) ∨ (¬ p225) ∨ (¬ p344)) : (¬ p103) ∨ (¬ p124) ∨ (¬ p213) ∨ (¬ p225) ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p213 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14738 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19360 (p7 p8 p164 p225 p980 p1055 p1324 : Prop)
    (h16152 : (¬ p7))
    (h789 : p164)
    (h16309 : (¬ p1324))
    (h14739 : p7 ∨ (¬ p8) ∨ (¬ p164) ∨ (¬ p225) ∨ (¬ p980) ∨ (¬ p1055) ∨ p1324) : (¬ p8) ∨ (¬ p225) ∨ (¬ p980) ∨ (¬ p1055) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p225 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p164 := by
    exact h789
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h14739 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step19361 (p7 p40 p69 p164 p225 p904 p1096 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h789 : p164)
    (h14740 : p7 ∨ p40 ∨ (¬ p69) ∨ (¬ p164) ∨ (¬ p225) ∨ (¬ p904) ∨ (¬ p1096)) : (¬ p69) ∨ (¬ p225) ∨ (¬ p904) ∨ (¬ p1096) := by
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
  have u6 : p164 := by
    exact h789
  rcases h14740 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19362 (p7 p8 p18 p71 p127 p164 p225 p423 p1040 p1055 p1136 : Prop)
    (h16152 : (¬ p7))
    (h789 : p164)
    (h16259 : (¬ p1136))
    (h14741 : p7 ∨ (¬ p8) ∨ (¬ p18) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p164) ∨ (¬ p225) ∨ (¬ p423) ∨ (¬ p1040) ∨ (¬ p1055) ∨ p1136) : (¬ p8) ∨ (¬ p18) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p225) ∨ (¬ p423) ∨ (¬ p1040) ∨ (¬ p1055) := by
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
  have u2 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1040 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p164 := by
    exact h789
  have u10 : (¬ p1136) := by
    exact h16259
  rcases h14741 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (u10 q10)

theorem step19363 (p7 p167 p424 p543 p882 p897 : Prop)
    (h16152 : (¬ p7))
    (h14742 : p7 ∨ (¬ p167) ∨ (¬ p424) ∨ (¬ p543) ∨ (¬ p882) ∨ (¬ p897)) : (¬ p167) ∨ (¬ p424) ∨ (¬ p543) ∨ (¬ p882) ∨ (¬ p897) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p543 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p882 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14742 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19364 (p7 p18 p128 p142 p302 p419 p796 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16285 : (¬ p302))
    (h14743 : p7 ∨ (¬ p18) ∨ (¬ p128) ∨ (¬ p142) ∨ p302 ∨ (¬ p419) ∨ (¬ p796)) : (¬ p18) ∨ (¬ p142) ∨ (¬ p419) ∨ (¬ p796) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p142 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p128 := by
    exact h653
  have u6 : (¬ p302) := by
    exact h16285
  rcases h14743 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19365 (p7 p16 p189 p227 p302 p419 p456 p498 p633 p796 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h6478 : p1075)
    (h14744 : p7 ∨ (¬ p16) ∨ (¬ p189) ∨ (¬ p227) ∨ p302 ∨ (¬ p419) ∨ (¬ p456) ∨ (¬ p498) ∨ (¬ p633) ∨ (¬ p796) ∨ (¬ p1075)) : (¬ p16) ∨ (¬ p189) ∨ (¬ p227) ∨ (¬ p419) ∨ (¬ p456) ∨ (¬ p498) ∨ (¬ p633) ∨ (¬ p796) := by
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
  have u2 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
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
  have u9 : (¬ p302) := by
    exact h16285
  have u10 : p1075 := by
    exact h6478
  rcases h14744 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19366 (p15 p128 p228 p383 p1136 : Prop)
    (h653 : p128)
    (h16259 : (¬ p1136))
    (h14746 : (¬ p15) ∨ (¬ p128) ∨ p228 ∨ (¬ p383) ∨ p1136) : (¬ p15) ∨ p228 ∨ (¬ p383) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p228) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p383 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p128 := by
    exact h653
  have u4 : (¬ p1136) := by
    exact h16259
  rcases h14746 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (u4 q4)

theorem step19367 (p7 p23 p107 p134 p163 p636 : Prop)
    (h16152 : (¬ p7))
    (h14748 : p7 ∨ (¬ p23) ∨ (¬ p107) ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p636)) : (¬ p23) ∨ (¬ p107) ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p636) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14748 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19369 (p7 p224 p406 p680 p897 p1104 : Prop)
    (h16152 : (¬ p7))
    (h14750 : p7 ∨ (¬ p224) ∨ (¬ p406) ∨ (¬ p680) ∨ (¬ p897) ∨ (¬ p1104)) : (¬ p224) ∨ (¬ p406) ∨ (¬ p680) ∨ (¬ p897) ∨ (¬ p1104) := by
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
  have u2 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14750 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19370 (p6 p7 p12 p140 p163 p191 p258 p346 p668 : Prop)
    (h16152 : (¬ p7))
    (h14751 : (¬ p6) ∨ p7 ∨ (¬ p12) ∨ (¬ p140) ∨ (¬ p163) ∨ (¬ p191) ∨ (¬ p258) ∨ (¬ p346) ∨ (¬ p668)) : (¬ p6) ∨ (¬ p12) ∨ (¬ p140) ∨ (¬ p163) ∨ (¬ p191) ∨ (¬ p258) ∨ (¬ p346) ∨ (¬ p668) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14751 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19371 (p7 p14 p20 p109 p207 p362 p420 : Prop)
    (h16152 : (¬ p7))
    (h14752 : p7 ∨ (¬ p14) ∨ (¬ p20) ∨ (¬ p109) ∨ (¬ p207) ∨ (¬ p362) ∨ (¬ p420)) : (¬ p14) ∨ (¬ p20) ∨ (¬ p109) ∨ (¬ p207) ∨ (¬ p362) ∨ (¬ p420) := by
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
  have u4 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14752 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19372 (p3 p6 p7 p12 p129 p142 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h6761 : p1139)
    (h14753 : (¬ p3) ∨ (¬ p6) ∨ p7 ∨ (¬ p12) ∨ p129 ∨ (¬ p142) ∨ (¬ p1139)) : (¬ p3) ∨ (¬ p6) ∨ (¬ p12) ∨ (¬ p142) := by
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
  have u3 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p1139 := by
    exact h6761
  rcases h14753 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u4 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19373 (p6 p7 p129 p142 p328 p387 p481 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h6744 : p1135)
    (h14754 : (¬ p6) ∨ p7 ∨ p129 ∨ (¬ p142) ∨ (¬ p328) ∨ (¬ p387) ∨ (¬ p481) ∨ (¬ p1135)) : (¬ p6) ∨ (¬ p142) ∨ (¬ p328) ∨ (¬ p387) ∨ (¬ p481) := by
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
  have u2 : p328 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p1135 := by
    exact h6744
  rcases h14754 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step19374 (p7 p20 p46 p142 p207 p362 p420 : Prop)
    (h16152 : (¬ p7))
    (h14755 : p7 ∨ (¬ p20) ∨ (¬ p46) ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p362) ∨ (¬ p420)) : (¬ p20) ∨ (¬ p46) ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p362) ∨ (¬ p420) := by
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
  have u3 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14755 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19375 (p6 p7 p142 p171 p188 p237 : Prop)
    (h16152 : (¬ p7))
    (h14756 : (¬ p6) ∨ p7 ∨ (¬ p142) ∨ (¬ p171) ∨ (¬ p188) ∨ (¬ p237)) : (¬ p6) ∨ (¬ p142) ∨ (¬ p171) ∨ (¬ p188) ∨ (¬ p237) := by
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
  have u2 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14756 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19376 (p2 p3 p7 p172 p540 p840 : Prop)
    (h16152 : (¬ p7))
    (h14757 : (¬ p2) ∨ (¬ p3) ∨ p7 ∨ (¬ p172) ∨ (¬ p540) ∨ (¬ p840)) : (¬ p2) ∨ (¬ p3) ∨ (¬ p172) ∨ (¬ p540) ∨ (¬ p840) := by
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
  have u2 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14757 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19377 (p7 p387 p426 p499 p601 p836 p1055 p1103 p1116 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h6744 : p1135)
    (h14758 : p7 ∨ (¬ p387) ∨ p426 ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p836) ∨ (¬ p1055) ∨ (¬ p1103) ∨ (¬ p1116) ∨ (¬ p1135)) : (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p836) ∨ (¬ p1055) ∨ (¬ p1103) ∨ (¬ p1116) := by
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
  have u8 : (¬ p426) := by
    exact h16178
  have u9 : p1135 := by
    exact h6744
  rcases h14758 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u8 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u9)

theorem step19378 (p3 p7 p43 p187 p229 p422 p792 p1324 p1465 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16309 : (¬ p1324))
    (h14759 : (¬ p3) ∨ p7 ∨ (¬ p43) ∨ (¬ p187) ∨ (¬ p229) ∨ (¬ p422) ∨ (¬ p792) ∨ p1324 ∨ (¬ p1465)) : (¬ p3) ∨ (¬ p43) ∨ (¬ p187) ∨ (¬ p229) ∨ (¬ p422) ∨ (¬ p1465) := by
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
  have u2 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p422 := by
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
  have u8 : (¬ p1324) := by
    exact h16309
  rcases h14759 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u7)
  · exact False.elim (u8 q7)
  · exact False.elim (q8 u5)

theorem step19379 (p3 p6 p7 p23 p126 p128 p229 p256 p420 p791 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16213 : (¬ p791))
    (h14760 : (¬ p3) ∨ (¬ p6) ∨ p7 ∨ (¬ p23) ∨ (¬ p126) ∨ (¬ p128) ∨ (¬ p229) ∨ (¬ p256) ∨ (¬ p420) ∨ p791) : (¬ p3) ∨ (¬ p6) ∨ (¬ p23) ∨ (¬ p126) ∨ (¬ p229) ∨ (¬ p256) ∨ (¬ p420) := by
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
  have u2 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p128 := by
    exact h653
  have u9 : (¬ p791) := by
    exact h16213
  rcases h14760 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (u9 q9)

theorem step19380 (p7 p362 p420 p455 p498 p983 p1056 p1081 p1103 p1226 : Prop)
    (h16152 : (¬ p7))
    (h14761 : p7 ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p455) ∨ (¬ p498) ∨ (¬ p983) ∨ (¬ p1056) ∨ (¬ p1081) ∨ (¬ p1103) ∨ (¬ p1226)) : (¬ p362) ∨ (¬ p420) ∨ (¬ p455) ∨ (¬ p498) ∨ (¬ p983) ∨ (¬ p1056) ∨ (¬ p1081) ∨ (¬ p1103) ∨ (¬ p1226) := by
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
  have u2 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p498 := by
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
  have u7 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14761 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19381 (p6 p72 p128 p257 : Prop)
    (h653 : p128)
    (h16170 : (¬ p257))
    (h14762 : (¬ p6) ∨ p72 ∨ (¬ p128) ∨ p257) : (¬ p6) ∨ p72 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p72) := fun hu => hn (Or.inr hu)
  have u2 : p128 := by
    exact h653
  have u3 : (¬ p257) := by
    exact h16170
  rcases h14762 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)

theorem step19382 (p3 p6 p7 p229 p257 p423 p1708 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h10766 : p1708)
    (h14763 : (¬ p3) ∨ (¬ p6) ∨ p7 ∨ (¬ p229) ∨ p257 ∨ (¬ p423) ∨ (¬ p1708)) : (¬ p3) ∨ (¬ p6) ∨ (¬ p229) ∨ (¬ p423) := by
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
  have u2 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p257) := by
    exact h16170
  have u6 : p1708 := by
    exact h10766
  rcases h14763 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u4 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19383 (p3 p7 p63 p128 p229 p789 p1004 p1136 p1159 p1393 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16259 : (¬ p1136))
    (h14764 : (¬ p3) ∨ p7 ∨ (¬ p63) ∨ (¬ p128) ∨ (¬ p229) ∨ (¬ p789) ∨ (¬ p1004) ∨ p1136 ∨ (¬ p1159) ∨ (¬ p1393)) : (¬ p3) ∨ (¬ p63) ∨ (¬ p229) ∨ (¬ p789) ∨ (¬ p1004) ∨ (¬ p1159) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p229 := by
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
  rcases h14764 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u9 q7)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step19384 (p7 p63 p862 p1135 p1136 p1325 p1393 p1508 : Prop)
    (h16152 : (¬ p7))
    (h6744 : p1135)
    (h16259 : (¬ p1136))
    (h14765 : p7 ∨ (¬ p63) ∨ (¬ p862) ∨ (¬ p1135) ∨ p1136 ∨ (¬ p1325) ∨ (¬ p1393) ∨ (¬ p1508)) : (¬ p63) ∨ (¬ p862) ∨ (¬ p1325) ∨ (¬ p1393) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p862 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p1135 := by
    exact h6744
  have u7 : (¬ p1136) := by
    exact h16259
  rcases h14765 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step19385 (p2 p7 p456 p633 p875 p1075 p1140 p1211 : Prop)
    (h16152 : (¬ p7))
    (h16220 : (¬ p875))
    (h6478 : p1075)
    (h14766 : (¬ p2) ∨ p7 ∨ (¬ p456) ∨ (¬ p633) ∨ p875 ∨ (¬ p1075) ∨ (¬ p1140) ∨ (¬ p1211)) : (¬ p2) ∨ (¬ p456) ∨ (¬ p633) ∨ (¬ p1140) ∨ (¬ p1211) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p875) := by
    exact h16220
  have u7 : p1075 := by
    exact h6478
  rcases h14766 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step19386 (p7 p63 p980 p1022 p1055 p1103 p1330 p1393 : Prop)
    (h16152 : (¬ p7))
    (h14767 : p7 ∨ (¬ p63) ∨ (¬ p980) ∨ (¬ p1022) ∨ (¬ p1055) ∨ (¬ p1103) ∨ (¬ p1330) ∨ (¬ p1393)) : (¬ p63) ∨ (¬ p980) ∨ (¬ p1022) ∨ (¬ p1055) ∨ (¬ p1103) ∨ (¬ p1330) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1022 := by
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
  rcases h14767 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19387 (p7 p16 p185 p362 p420 p455 p498 p1081 p1115 : Prop)
    (h16152 : (¬ p7))
    (h14768 : p7 ∨ (¬ p16) ∨ (¬ p185) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p455) ∨ (¬ p498) ∨ (¬ p1081) ∨ (¬ p1115)) : (¬ p16) ∨ (¬ p185) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p455) ∨ (¬ p498) ∨ (¬ p1081) ∨ (¬ p1115) := by
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
  have u2 : p362 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14768 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19388 (p7 p23 p134 p456 p1211 p1256 : Prop)
    (h16152 : (¬ p7))
    (h14769 : p7 ∨ (¬ p23) ∨ (¬ p134) ∨ (¬ p456) ∨ (¬ p1211) ∨ (¬ p1256)) : (¬ p23) ∨ (¬ p134) ∨ (¬ p456) ∨ (¬ p1211) ∨ (¬ p1256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14769 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19389 (p3 p7 p43 p187 p227 p229 p422 p498 p792 p1004 p1136 p1325 p1452 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16259 : (¬ p1136))
    (h14770 : (¬ p3) ∨ p7 ∨ (¬ p43) ∨ (¬ p187) ∨ (¬ p227) ∨ (¬ p229) ∨ (¬ p422) ∨ (¬ p498) ∨ (¬ p792) ∨ (¬ p1004) ∨ p1136 ∨ (¬ p1325) ∨ (¬ p1452)) : (¬ p3) ∨ (¬ p43) ∨ (¬ p187) ∨ (¬ p227) ∨ (¬ p229) ∨ (¬ p422) ∨ (¬ p498) ∨ (¬ p1004) ∨ (¬ p1325) ∨ (¬ p1452) := by
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
  have u2 : p187 := by
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
  have u5 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : p792 := by
    exact h4535
  have u12 : (¬ p1136) := by
    exact h16259
  rcases h14770 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (q0 u0)
  · exact False.elim (u10 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u11)
  · exact False.elim (q9 u7)
  · exact False.elim (u12 q10)
  · exact False.elim (q11 u8)
  · exact False.elim (q12 u9)

theorem step19390 (p2 p3 p7 p534 p540 p738 : Prop)
    (h16152 : (¬ p7))
    (h14771 : (¬ p2) ∨ (¬ p3) ∨ p7 ∨ (¬ p534) ∨ (¬ p540) ∨ (¬ p738)) : (¬ p2) ∨ (¬ p3) ∨ (¬ p534) ∨ (¬ p540) ∨ (¬ p738) := by
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
  have u2 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p738 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14771 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19391 (p7 p128 p170 p229 p537 p796 p875 p940 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16220 : (¬ p875))
    (h14773 : p7 ∨ (¬ p128) ∨ (¬ p170) ∨ (¬ p229) ∨ (¬ p537) ∨ (¬ p796) ∨ p875 ∨ (¬ p940)) : (¬ p170) ∨ (¬ p229) ∨ (¬ p537) ∨ (¬ p796) ∨ (¬ p940) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p128 := by
    exact h653
  have u7 : (¬ p875) := by
    exact h16220
  rcases h14773 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step19392 (p7 p16 p185 p362 p387 p498 p985 p1333 p1584 : Prop)
    (h16152 : (¬ p7))
    (h14774 : p7 ∨ (¬ p16) ∨ (¬ p185) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p498) ∨ (¬ p985) ∨ (¬ p1333) ∨ (¬ p1584)) : (¬ p16) ∨ (¬ p185) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p498) ∨ (¬ p985) ∨ (¬ p1333) ∨ (¬ p1584) := by
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
  have u2 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p498 := by
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
  rcases h14774 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19393 (p7 p160 p236 p456 p501 p532 : Prop)
    (h16152 : (¬ p7))
    (h14775 : p7 ∨ (¬ p160) ∨ (¬ p236) ∨ (¬ p456) ∨ (¬ p501) ∨ (¬ p532)) : (¬ p160) ∨ (¬ p236) ∨ (¬ p456) ∨ (¬ p501) ∨ (¬ p532) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p236 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p501 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14775 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19394 (p7 p14 p109 p134 p424 p1187 : Prop)
    (h16152 : (¬ p7))
    (h14776 : p7 ∨ (¬ p14) ∨ (¬ p109) ∨ (¬ p134) ∨ (¬ p424) ∨ (¬ p1187)) : (¬ p14) ∨ (¬ p109) ∨ (¬ p134) ∨ (¬ p424) ∨ (¬ p1187) := by
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
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14776 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19396 (p7 p90 p241 p256 p387 p574 p601 p669 p918 p1055 : Prop)
    (h16152 : (¬ p7))
    (h14779 : p7 ∨ (¬ p90) ∨ (¬ p241) ∨ (¬ p256) ∨ (¬ p387) ∨ (¬ p574) ∨ (¬ p601) ∨ (¬ p669) ∨ (¬ p918) ∨ (¬ p1055)) : (¬ p90) ∨ (¬ p241) ∨ (¬ p256) ∨ (¬ p387) ∨ (¬ p574) ∨ (¬ p601) ∨ (¬ p669) ∨ (¬ p918) ∨ (¬ p1055) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p574 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14779 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19397 (p7 p41 p207 p265 p576 p1213 p1256 : Prop)
    (h16152 : (¬ p7))
    (h14780 : p7 ∨ (¬ p41) ∨ (¬ p207) ∨ (¬ p265) ∨ (¬ p576) ∨ (¬ p1213) ∨ (¬ p1256)) : (¬ p41) ∨ (¬ p207) ∨ (¬ p265) ∨ (¬ p576) ∨ (¬ p1213) ∨ (¬ p1256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14780 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19398 (p7 p63 p126 p387 p581 p1135 p1136 : Prop)
    (h16152 : (¬ p7))
    (h6744 : p1135)
    (h16259 : (¬ p1136))
    (h14781 : p7 ∨ (¬ p63) ∨ (¬ p126) ∨ (¬ p387) ∨ (¬ p581) ∨ (¬ p1135) ∨ p1136) : (¬ p63) ∨ (¬ p126) ∨ (¬ p387) ∨ (¬ p581) := by
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
  have u2 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p1135 := by
    exact h6744
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h14781 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)

theorem step19399 (p6 p7 p14 p109 p1140 p1141 : Prop)
    (h16152 : (¬ p7))
    (h14782 : (¬ p6) ∨ p7 ∨ (¬ p14) ∨ (¬ p109) ∨ (¬ p1140) ∨ (¬ p1141)) : (¬ p6) ∨ (¬ p14) ∨ (¬ p109) ∨ (¬ p1140) ∨ (¬ p1141) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14782 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19400 (p7 p14 p38 p42 p167 p387 p499 p601 p1004 p1136 p1159 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16259 : (¬ p1136))
    (h14783 : p7 ∨ (¬ p14) ∨ (¬ p38) ∨ (¬ p42) ∨ (¬ p167) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1004) ∨ p1136 ∨ (¬ p1159)) : (¬ p14) ∨ (¬ p38) ∨ (¬ p167) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1004) ∨ (¬ p1159) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p167 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p42 := by
    exact h132
  have u10 : (¬ p1136) := by
    exact h16259
  rcases h14783 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19401 (p7 p42 p63 p422 p581 p983 p1081 p1136 p1145 p1226 p1235 p1443 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16259 : (¬ p1136))
    (h14785 : p7 ∨ (¬ p42) ∨ (¬ p63) ∨ (¬ p422) ∨ (¬ p581) ∨ (¬ p983) ∨ (¬ p1081) ∨ p1136 ∨ (¬ p1145) ∨ (¬ p1226) ∨ (¬ p1235) ∨ (¬ p1443)) : (¬ p63) ∨ (¬ p422) ∨ (¬ p581) ∨ (¬ p983) ∨ (¬ p1081) ∨ (¬ p1145) ∨ (¬ p1226) ∨ (¬ p1235) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p422 := by
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
  have u4 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1145 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1235 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p42 := by
    exact h132
  have u11 : (¬ p1136) := by
    exact h16259
  rcases h14785 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u11 q7)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step19402 (p3 p7 p128 p229 p387 p499 p601 p1004 p1136 p1159 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16259 : (¬ p1136))
    (h14786 : (¬ p3) ∨ p7 ∨ (¬ p128) ∨ (¬ p229) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1004) ∨ p1136 ∨ (¬ p1159)) : (¬ p3) ∨ (¬ p229) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1004) ∨ (¬ p1159) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1004 := by
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
  rcases h14786 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u9 q8)
  · exact False.elim (q9 u6)

theorem step19404 (p7 p256 p576 p814 p1273 p1491 p1527 : Prop)
    (h16152 : (¬ p7))
    (h9051 : p1491)
    (h16359 : (¬ p1527))
    (h14788 : p7 ∨ (¬ p256) ∨ (¬ p576) ∨ (¬ p814) ∨ (¬ p1273) ∨ (¬ p1491) ∨ p1527) : (¬ p256) ∨ (¬ p576) ∨ (¬ p814) ∨ (¬ p1273) := by
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
  have u3 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p1491 := by
    exact h9051
  have u6 : (¬ p1527) := by
    exact h16359
  rcases h14788 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)

theorem step19405 (p7 p89 p128 p229 p256 p560 p576 p983 p1056 p1120 p1136 p1226 p1273 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16259 : (¬ p1136))
    (h14789 : p7 ∨ (¬ p89) ∨ (¬ p128) ∨ (¬ p229) ∨ (¬ p256) ∨ (¬ p560) ∨ (¬ p576) ∨ (¬ p983) ∨ (¬ p1056) ∨ (¬ p1120) ∨ p1136 ∨ (¬ p1226) ∨ (¬ p1273)) : (¬ p89) ∨ (¬ p229) ∨ (¬ p256) ∨ (¬ p560) ∨ (¬ p576) ∨ (¬ p983) ∨ (¬ p1056) ∨ (¬ p1120) ∨ (¬ p1226) ∨ (¬ p1273) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
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
  have u7 : p1120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : p128 := by
    exact h653
  have u12 : (¬ p1136) := by
    exact h16259
  rcases h14789 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (u12 q10)
  · exact False.elim (q11 u8)
  · exact False.elim (q12 u9)

theorem step19406 (p7 p128 p229 p434 p499 p560 p601 p980 p1055 p1136 p1330 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16259 : (¬ p1136))
    (h14790 : p7 ∨ (¬ p128) ∨ (¬ p229) ∨ (¬ p434) ∨ (¬ p499) ∨ (¬ p560) ∨ (¬ p601) ∨ (¬ p980) ∨ (¬ p1055) ∨ p1136 ∨ (¬ p1330)) : (¬ p229) ∨ (¬ p434) ∨ (¬ p499) ∨ (¬ p560) ∨ (¬ p601) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1330) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p229 := by
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
  have u3 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p128 := by
    exact h653
  have u10 : (¬ p1136) := by
    exact h16259
  rcases h14790 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (u10 q9)
  · exact False.elim (q10 u7)

theorem step19407 (p7 p89 p256 p387 p518 p576 p1135 p1136 p1393 : Prop)
    (h16152 : (¬ p7))
    (h6744 : p1135)
    (h16259 : (¬ p1136))
    (h14791 : p7 ∨ (¬ p89) ∨ (¬ p256) ∨ (¬ p387) ∨ (¬ p518) ∨ (¬ p576) ∨ (¬ p1135) ∨ p1136 ∨ (¬ p1393)) : (¬ p89) ∨ (¬ p256) ∨ (¬ p387) ∨ (¬ p518) ∨ (¬ p576) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p518 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : p1135 := by
    exact h6744
  have u8 : (¬ p1136) := by
    exact h16259
  rcases h14791 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u7)
  · exact False.elim (u8 q7)
  · exact False.elim (q8 u5)

theorem step19408 (p2 p5 p7 p387 p431 p435 p499 p601 : Prop)
    (h16152 : (¬ p7))
    (h14792 : (¬ p2) ∨ (¬ p5) ∨ p7 ∨ (¬ p387) ∨ (¬ p431) ∨ (¬ p435) ∨ (¬ p499) ∨ (¬ p601)) : (¬ p2) ∨ (¬ p5) ∨ (¬ p387) ∨ (¬ p431) ∨ (¬ p435) ∨ (¬ p499) ∨ (¬ p601) := by
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
  have u2 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p435 := by
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
  rcases h14792 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19409 (p7 p87 p185 p262 p362 p387 p581 p669 p1115 : Prop)
    (h16152 : (¬ p7))
    (h14793 : p7 ∨ (¬ p87) ∨ (¬ p185) ∨ (¬ p262) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p581) ∨ (¬ p669) ∨ (¬ p1115)) : (¬ p87) ∨ (¬ p185) ∨ (¬ p262) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p581) ∨ (¬ p669) ∨ (¬ p1115) := by
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
  have u3 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14793 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19410 (p7 p19 p40 p185 p207 p279 p362 p387 p864 p928 p1249 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h1444 : p279)
    (h14794 : p7 ∨ (¬ p19) ∨ p40 ∨ (¬ p185) ∨ (¬ p207) ∨ (¬ p279) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p864) ∨ (¬ p928) ∨ (¬ p1249)) : (¬ p19) ∨ (¬ p185) ∨ (¬ p207) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p864) ∨ (¬ p928) ∨ (¬ p1249) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p185 := by
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
  have u4 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p40) := by
    exact h16150
  have u10 : p279 := by
    exact h1444
  rcases h14794 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u9 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step19411 (p3 p6 p7 p107 p129 p142 p1077 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h6761 : p1139)
    (h14795 : (¬ p3) ∨ (¬ p6) ∨ p7 ∨ (¬ p107) ∨ p129 ∨ (¬ p142) ∨ (¬ p1077) ∨ (¬ p1139)) : (¬ p3) ∨ (¬ p6) ∨ (¬ p107) ∨ (¬ p142) ∨ (¬ p1077) := by
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
  have u4 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p1139 := by
    exact h6761
  rcases h14795 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step19412 (p6 p42 p195 p257 : Prop)
    (h132 : p42)
    (h16170 : (¬ p257))
    (h14796 : (¬ p6) ∨ (¬ p42) ∨ p195 ∨ p257) : (¬ p6) ∨ p195 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p195) := fun hu => hn (Or.inr hu)
  have u2 : p42 := by
    exact h132
  have u3 : (¬ p257) := by
    exact h16170
  rcases h14796 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u3 q3)

theorem step19413 (p7 p157 p160 p668 p710 p980 : Prop)
    (h16152 : (¬ p7))
    (h14797 : p7 ∨ (¬ p157) ∨ (¬ p160) ∨ (¬ p668) ∨ (¬ p710) ∨ (¬ p980)) : (¬ p157) ∨ (¬ p160) ∨ (¬ p668) ∨ (¬ p710) ∨ (¬ p980) := by
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
  have u2 : p668 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14797 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19416 (p3 p6 p7 p129 p142 p172 p1074 p1099 p1116 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h7053 : p1184)
    (h14800 : (¬ p3) ∨ (¬ p6) ∨ p7 ∨ p129 ∨ (¬ p142) ∨ (¬ p172) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1116) ∨ (¬ p1184)) : (¬ p3) ∨ (¬ p6) ∨ (¬ p142) ∨ (¬ p172) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1116) := by
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
  have u4 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p129) := by
    exact h16154
  have u9 : p1184 := by
    exact h7053
  rcases h14800 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19417 (p7 p109 p136 p163 p207 p301 p362 : Prop)
    (h16152 : (¬ p7))
    (h14801 : p7 ∨ (¬ p109) ∨ (¬ p136) ∨ (¬ p163) ∨ (¬ p207) ∨ (¬ p301) ∨ (¬ p362)) : (¬ p109) ∨ (¬ p136) ∨ (¬ p163) ∨ (¬ p207) ∨ (¬ p301) ∨ (¬ p362) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p136 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14801 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19418 (p7 p45 p85 p134 p257 p362 p387 p496 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h8348 : p1386)
    (h14802 : p7 ∨ (¬ p45) ∨ (¬ p85) ∨ (¬ p134) ∨ p257 ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p496) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p45) ∨ (¬ p85) ∨ (¬ p134) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p496) ∨ (¬ p1333) := by
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
  have u3 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p496 := by
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
  rcases h14802 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19419 (p7 p41 p83 p123 p189 p362 p387 p496 p576 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h8348 : p1386)
    (h14803 : p7 ∨ (¬ p41) ∨ (¬ p83) ∨ p123 ∨ (¬ p189) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p496) ∨ (¬ p576) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p41) ∨ (¬ p83) ∨ (¬ p189) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p496) ∨ (¬ p576) ∨ (¬ p1333) := by
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
  have u3 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p576 := by
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
  rcases h14803 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19420 (p7 p227 p496 p669 p1074 p1099 p1325 p1452 : Prop)
    (h16152 : (¬ p7))
    (h14804 : p7 ∨ (¬ p227) ∨ (¬ p496) ∨ (¬ p669) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1325) ∨ (¬ p1452)) : (¬ p227) ∨ (¬ p496) ∨ (¬ p669) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1325) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p669 := by
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
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14804 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19421 (p7 p63 p160 p405 p615 p669 p1074 p1099 p1325 p1389 : Prop)
    (h16152 : (¬ p7))
    (h14805 : p7 ∨ (¬ p63) ∨ (¬ p160) ∨ (¬ p405) ∨ (¬ p615) ∨ (¬ p669) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1325) ∨ (¬ p1389)) : (¬ p63) ∨ (¬ p160) ∨ (¬ p405) ∨ (¬ p615) ∨ (¬ p669) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1325) ∨ (¬ p1389) := by
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
  have u2 : p405 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p615 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14805 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19422 (p3 p7 p41 p109 p137 p187 p576 : Prop)
    (h16152 : (¬ p7))
    (h14806 : (¬ p3) ∨ p7 ∨ (¬ p41) ∨ (¬ p109) ∨ (¬ p137) ∨ (¬ p187) ∨ (¬ p576)) : (¬ p3) ∨ (¬ p41) ∨ (¬ p109) ∨ (¬ p137) ∨ (¬ p187) ∨ (¬ p576) := by
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
  have u2 : p109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p137 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14806 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19423 (p7 p129 p387 p424 p438 p1135 p1366 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h6744 : p1135)
    (h14807 : p7 ∨ p129 ∨ (¬ p387) ∨ (¬ p424) ∨ (¬ p438) ∨ (¬ p1135) ∨ (¬ p1366)) : (¬ p387) ∨ (¬ p424) ∨ (¬ p438) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p438 := by
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
  rcases h14807 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step19424 (p7 p87 p124 p185 p262 p581 p668 p897 p926 p1077 : Prop)
    (h16152 : (¬ p7))
    (h14808 : p7 ∨ (¬ p87) ∨ (¬ p124) ∨ (¬ p185) ∨ (¬ p262) ∨ (¬ p581) ∨ (¬ p668) ∨ (¬ p897) ∨ (¬ p926) ∨ (¬ p1077)) : (¬ p87) ∨ (¬ p124) ∨ (¬ p185) ∨ (¬ p262) ∨ (¬ p581) ∨ (¬ p668) ∨ (¬ p897) ∨ (¬ p926) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14808 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19425 (p7 p134 p257 p980 p1035 p1139 p1256 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h6761 : p1139)
    (h14809 : p7 ∨ (¬ p134) ∨ p257 ∨ (¬ p980) ∨ (¬ p1035) ∨ (¬ p1139) ∨ (¬ p1256)) : (¬ p134) ∨ (¬ p980) ∨ (¬ p1035) ∨ (¬ p1256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p980 := by
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
  have u5 : (¬ p257) := by
    exact h16170
  have u6 : p1139 := by
    exact h6761
  rcases h14809 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step19426 (p7 p45 p83 p134 p185 p257 p928 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h7053 : p1184)
    (h14810 : p7 ∨ (¬ p45) ∨ (¬ p83) ∨ (¬ p134) ∨ (¬ p185) ∨ p257 ∨ (¬ p928) ∨ (¬ p1184)) : (¬ p45) ∨ (¬ p83) ∨ (¬ p134) ∨ (¬ p185) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p257) := by
    exact h16170
  have u7 : p1184 := by
    exact h7053
  rcases h14810 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step19428 (p7 p85 p426 p728 p1015 p1184 p1385 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h7053 : p1184)
    (h14812 : p7 ∨ (¬ p85) ∨ p426 ∨ (¬ p728) ∨ (¬ p1015) ∨ (¬ p1184) ∨ (¬ p1385)) : (¬ p85) ∨ (¬ p728) ∨ (¬ p1015) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p728 := by
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
  have u5 : (¬ p426) := by
    exact h16178
  have u6 : p1184 := by
    exact h7053
  rcases h14812 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step19429 (p7 p124 p129 p142 p207 p344 p657 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h6744 : p1135)
    (h14813 : p7 ∨ (¬ p124) ∨ p129 ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p344) ∨ (¬ p657) ∨ (¬ p1135)) : (¬ p124) ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p344) ∨ (¬ p657) := by
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
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p1135 := by
    exact h6744
  rcases h14813 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step19430 (p7 p142 p191 p207 p226 p362 p387 p669 p1036 : Prop)
    (h16152 : (¬ p7))
    (h14814 : p7 ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p207) ∨ (¬ p226) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p669) ∨ (¬ p1036)) : (¬ p142) ∨ (¬ p191) ∨ (¬ p207) ∨ (¬ p226) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p669) ∨ (¬ p1036) := by
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
  have u2 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p226 := by
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
  have u6 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14814 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19431 (p7 p156 p193 p238 p710 p840 : Prop)
    (h16152 : (¬ p7))
    (h14815 : p7 ∨ (¬ p156) ∨ (¬ p193) ∨ (¬ p238) ∨ (¬ p710) ∨ (¬ p840)) : (¬ p156) ∨ (¬ p193) ∨ (¬ p238) ∨ (¬ p710) ∨ (¬ p840) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p238 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14815 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19432 (p5 p7 p23 p134 p163 p226 p362 p420 p498 : Prop)
    (h16152 : (¬ p7))
    (h14816 : (¬ p5) ∨ p7 ∨ (¬ p23) ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p498)) : (¬ p5) ∨ (¬ p23) ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p498) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14816 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19434 (p2 p5 p7 p110 p167 p424 p499 p633 : Prop)
    (h16152 : (¬ p7))
    (h14818 : (¬ p2) ∨ (¬ p5) ∨ p7 ∨ (¬ p110) ∨ (¬ p167) ∨ (¬ p424) ∨ (¬ p499) ∨ (¬ p633)) : (¬ p2) ∨ (¬ p5) ∨ (¬ p110) ∨ (¬ p167) ∨ (¬ p424) ∨ (¬ p499) ∨ (¬ p633) := by
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
  have u2 : p110 := by
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
  have u6 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14818 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19435 (p7 p16 p110 p167 p189 p362 p420 p498 p633 : Prop)
    (h16152 : (¬ p7))
    (h14819 : p7 ∨ (¬ p16) ∨ (¬ p110) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p498) ∨ (¬ p633)) : (¬ p16) ∨ (¬ p110) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p498) ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
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
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14819 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19436 (p7 p134 p1213 p1250 p1465 p1508 : Prop)
    (h16152 : (¬ p7))
    (h14821 : p7 ∨ (¬ p134) ∨ (¬ p1213) ∨ (¬ p1250) ∨ (¬ p1465) ∨ (¬ p1508)) : (¬ p134) ∨ (¬ p1213) ∨ (¬ p1250) ∨ (¬ p1465) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1250 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14821 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19437 (p7 p256 p387 p518 p576 p791 p1135 p1393 : Prop)
    (h16152 : (¬ p7))
    (h16213 : (¬ p791))
    (h6744 : p1135)
    (h14823 : p7 ∨ (¬ p256) ∨ (¬ p387) ∨ (¬ p518) ∨ (¬ p576) ∨ p791 ∨ (¬ p1135) ∨ (¬ p1393)) : (¬ p256) ∨ (¬ p387) ∨ (¬ p518) ∨ (¬ p576) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p387 := by
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
  have u6 : (¬ p791) := by
    exact h16213
  have u7 : p1135 := by
    exact h6744
  rcases h14823 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step19438 (p7 p45 p387 p499 p601 p792 p1004 p1035 p1136 p1252 p1489 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16259 : (¬ p1136))
    (h14824 : p7 ∨ (¬ p45) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p792) ∨ (¬ p1004) ∨ (¬ p1035) ∨ p1136 ∨ (¬ p1252) ∨ (¬ p1489)) : (¬ p45) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1004) ∨ (¬ p1035) ∨ (¬ p1252) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1252 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p792 := by
    exact h4535
  have u10 : (¬ p1136) := by
    exact h16259
  rcases h14824 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u10 q8)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step19439 (p7 p23 p108 p309 p544 p636 p710 : Prop)
    (h16152 : (¬ p7))
    (h14825 : p7 ∨ (¬ p23) ∨ (¬ p108) ∨ (¬ p309) ∨ (¬ p544) ∨ (¬ p636) ∨ (¬ p710)) : (¬ p23) ∨ (¬ p108) ∨ (¬ p309) ∨ (¬ p544) ∨ (¬ p636) ∨ (¬ p710) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14825 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19440 (p7 p12 p23 p108 p309 p636 p1055 : Prop)
    (h16152 : (¬ p7))
    (h14826 : p7 ∨ (¬ p12) ∨ (¬ p23) ∨ (¬ p108) ∨ (¬ p309) ∨ (¬ p636) ∨ (¬ p1055)) : (¬ p12) ∨ (¬ p23) ∨ (¬ p108) ∨ (¬ p309) ∨ (¬ p636) ∨ (¬ p1055) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14826 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19441 (p7 p45 p193 p238 p544 p653 p710 p792 : Prop)
    (h16152 : (¬ p7))
    (h16194 : (¬ p653))
    (h4535 : p792)
    (h14827 : p7 ∨ (¬ p45) ∨ (¬ p193) ∨ (¬ p238) ∨ (¬ p544) ∨ p653 ∨ (¬ p710) ∨ (¬ p792)) : (¬ p45) ∨ (¬ p193) ∨ (¬ p238) ∨ (¬ p544) ∨ (¬ p710) := by
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
  have u2 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p653) := by
    exact h16194
  have u7 : p792 := by
    exact h4535
  rcases h14827 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step19442 (p7 p45 p185 p193 p792 p1115 p1181 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16272 : (¬ p1181))
    (h14828 : p7 ∨ (¬ p45) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p792) ∨ (¬ p1115) ∨ p1181) : (¬ p45) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p1115) := by
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
  have u3 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p792 := by
    exact h4535
  have u6 : (¬ p1181) := by
    exact h16272
  rcases h14828 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step19443 (p7 p45 p166 p185 p193 p225 p426 p792 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h4535 : p792)
    (h14829 : p7 ∨ (¬ p45) ∨ (¬ p166) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p225) ∨ p426 ∨ (¬ p792)) : (¬ p45) ∨ (¬ p166) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p426) := by
    exact h16178
  have u7 : p792 := by
    exact h4535
  rcases h14829 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u7)

theorem step19444 (p7 p41 p156 p710 p840 p922 p1102 : Prop)
    (h16152 : (¬ p7))
    (h14830 : p7 ∨ (¬ p41) ∨ (¬ p156) ∨ (¬ p710) ∨ (¬ p840) ∨ (¬ p922) ∨ (¬ p1102)) : (¬ p41) ∨ (¬ p156) ∨ (¬ p710) ∨ (¬ p840) ∨ (¬ p922) ∨ (¬ p1102) := by
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
  have u2 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p922 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14830 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19445 (p7 p12 p225 p387 p426 p499 p601 p1055 p1103 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h6744 : p1135)
    (h14831 : p7 ∨ (¬ p12) ∨ (¬ p225) ∨ (¬ p387) ∨ p426 ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1055) ∨ (¬ p1103) ∨ (¬ p1135)) : (¬ p12) ∨ (¬ p225) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1055) ∨ (¬ p1103) := by
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
  have u2 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p601 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p426) := by
    exact h16178
  have u9 : p1135 := by
    exact h6744
  rcases h14831 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19446 (p7 p41 p138 p262 p362 p420 p575 : Prop)
    (h16152 : (¬ p7))
    (h14832 : p7 ∨ (¬ p41) ∨ (¬ p138) ∨ (¬ p262) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p575)) : (¬ p41) ∨ (¬ p138) ∨ (¬ p262) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p575) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14832 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19447 (p5 p7 p226 p387 p499 p601 p669 p1036 : Prop)
    (h16152 : (¬ p7))
    (h14833 : (¬ p5) ∨ p7 ∨ (¬ p226) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p669) ∨ (¬ p1036)) : (¬ p5) ∨ (¬ p226) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p669) ∨ (¬ p1036) := by
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
  have u2 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14833 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19448 (p5 p7 p225 p226 p499 p633 p668 p1077 : Prop)
    (h16152 : (¬ p7))
    (h14835 : (¬ p5) ∨ p7 ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p668) ∨ (¬ p1077)) : (¬ p5) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p668) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
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
  have u3 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14835 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19450 (p7 p386 p499 p601 p1135 p1136 p1325 p1452 : Prop)
    (h16152 : (¬ p7))
    (h6744 : p1135)
    (h16259 : (¬ p1136))
    (h14837 : p7 ∨ (¬ p386) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1135) ∨ p1136 ∨ (¬ p1325) ∨ (¬ p1452)) : (¬ p386) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1325) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p386 := by
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
  have u6 : p1135 := by
    exact h6744
  have u7 : (¬ p1136) := by
    exact h16259
  rcases h14837 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (u7 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step19451 (p7 p45 p192 p226 p362 p420 p455 p498 p792 p1036 p1081 p1136 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16259 : (¬ p1136))
    (h14838 : p7 ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p226) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p455) ∨ (¬ p498) ∨ (¬ p792) ∨ (¬ p1036) ∨ (¬ p1081) ∨ p1136) : (¬ p45) ∨ (¬ p192) ∨ (¬ p226) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p455) ∨ (¬ p498) ∨ (¬ p1036) ∨ (¬ p1081) := by
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
  have u3 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p792 := by
    exact h4535
  have u11 : (¬ p1136) := by
    exact h16259
  rcases h14838 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
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

theorem step19452 (p7 p45 p192 p226 p227 p498 p669 p792 p1036 p1136 p1325 p1452 : Prop)
    (h16152 : (¬ p7))
    (h4535 : p792)
    (h16259 : (¬ p1136))
    (h14839 : p7 ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p226) ∨ (¬ p227) ∨ (¬ p498) ∨ (¬ p669) ∨ (¬ p792) ∨ (¬ p1036) ∨ p1136 ∨ (¬ p1325) ∨ (¬ p1452)) : (¬ p45) ∨ (¬ p192) ∨ (¬ p226) ∨ (¬ p227) ∨ (¬ p498) ∨ (¬ p669) ∨ (¬ p1036) ∨ (¬ p1325) ∨ (¬ p1452) := by
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
  have u3 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p792 := by
    exact h4535
  have u11 : (¬ p1136) := by
    exact h16259
  rcases h14839 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u6)
  · exact False.elim (u11 q9)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step19453 (p7 p17 p456 p578 p1346 p1495 : Prop)
    (h16152 : (¬ p7))
    (h14840 : p7 ∨ (¬ p17) ∨ (¬ p456) ∨ (¬ p578) ∨ (¬ p1346) ∨ (¬ p1495)) : (¬ p17) ∨ (¬ p456) ∨ (¬ p578) ∨ (¬ p1346) ∨ (¬ p1495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p578 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14840 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19454 (p7 p45 p192 p226 p362 p387 p658 p792 p940 p985 p1333 : Prop)
    (h16152 : (¬ p7))
    (h16199 : (¬ p658))
    (h4535 : p792)
    (h14841 : p7 ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p226) ∨ (¬ p362) ∨ (¬ p387) ∨ p658 ∨ (¬ p792) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1333)) : (¬ p45) ∨ (¬ p192) ∨ (¬ p226) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1333) := by
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
  have u3 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p387 := by
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
  have u7 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p658) := by
    exact h16199
  have u10 : p792 := by
    exact h4535
  rcases h14841 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19455 (p7 p17 p45 p123 p192 p225 p226 p237 p537 p738 p792 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h4535 : p792)
    (h14842 : p7 ∨ (¬ p17) ∨ (¬ p45) ∨ p123 ∨ (¬ p192) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p237) ∨ (¬ p537) ∨ (¬ p738) ∨ (¬ p792)) : (¬ p17) ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p237) ∨ (¬ p537) ∨ (¬ p738) := by
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
  have u6 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p738 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p123) := by
    exact h16186
  have u10 : p792 := by
    exact h4535
  rcases h14842 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19456 (p4 p7 p110 p420 p544 p633 : Prop)
    (h16152 : (¬ p7))
    (h14843 : (¬ p4) ∨ p7 ∨ (¬ p110) ∨ (¬ p420) ∨ (¬ p544) ∨ (¬ p633)) : (¬ p4) ∨ (¬ p110) ∨ (¬ p420) ∨ (¬ p544) ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14843 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19457 (p7 p124 p344 p420 p431 p438 p501 p657 : Prop)
    (h16152 : (¬ p7))
    (h14844 : p7 ∨ (¬ p124) ∨ (¬ p344) ∨ (¬ p420) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p501) ∨ (¬ p657)) : (¬ p124) ∨ (¬ p344) ∨ (¬ p420) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p501) ∨ (¬ p657) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p420 := by
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
  have u5 : p501 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14844 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19458 (p7 p124 p344 p657 p961 p1135 p1445 : Prop)
    (h16152 : (¬ p7))
    (h6744 : p1135)
    (h16350 : (¬ p1445))
    (h14845 : p7 ∨ (¬ p124) ∨ (¬ p344) ∨ (¬ p657) ∨ (¬ p961) ∨ (¬ p1135) ∨ p1445) : (¬ p124) ∨ (¬ p344) ∨ (¬ p657) ∨ (¬ p961) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p1135 := by
    exact h6744
  have u6 : (¬ p1445) := by
    exact h16350
  rcases h14845 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)

theorem step19459 (p7 p102 p126 p257 p258 p387 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h6744 : p1135)
    (h14846 : p7 ∨ (¬ p102) ∨ (¬ p126) ∨ p257 ∨ (¬ p258) ∨ (¬ p387) ∨ (¬ p1135)) : (¬ p102) ∨ (¬ p126) ∨ (¬ p258) ∨ (¬ p387) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p257) := by
    exact h16170
  have u6 : p1135 := by
    exact h6744
  rcases h14846 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19460 (p102 p122 p257 p1084 : Prop)
    (h10260 : p122)
    (h16170 : (¬ p257))
    (h14847 : (¬ p102) ∨ (¬ p122) ∨ p257 ∨ p1084) : (¬ p102) ∨ p1084 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1084) := fun hu => hn (Or.inr hu)
  have u2 : p122 := by
    exact h10260
  have u3 : (¬ p257) := by
    exact h16170
  rcases h14847 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (u3 q2)
  · exact False.elim (u1 q3)

theorem step19461 (p7 p45 p124 p193 p344 p657 p658 p792 p1004 p1253 p1349 : Prop)
    (h16152 : (¬ p7))
    (h16199 : (¬ p658))
    (h4535 : p792)
    (h14848 : p7 ∨ (¬ p45) ∨ (¬ p124) ∨ (¬ p193) ∨ (¬ p344) ∨ (¬ p657) ∨ p658 ∨ (¬ p792) ∨ (¬ p1004) ∨ (¬ p1253) ∨ (¬ p1349)) : (¬ p45) ∨ (¬ p124) ∨ (¬ p193) ∨ (¬ p344) ∨ (¬ p657) ∨ (¬ p1004) ∨ (¬ p1253) ∨ (¬ p1349) := by
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
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1253 := by
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
  rcases h14848 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19462 (p331 p387 p875 p1135 : Prop)
    (h16220 : (¬ p875))
    (h6744 : p1135)
    (h14849 : p331 ∨ (¬ p387) ∨ p875 ∨ (¬ p1135)) : p331 ∨ (¬ p387) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p331) := fun hu => hn (Or.inl hu)
  have u1 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p875) := by
    exact h16220
  have u3 : p1135 := by
    exact h6744
  rcases h14849 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)

theorem step19464 (p7 p124 p344 p657 p658 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16199 : (¬ p658))
    (h8348 : p1386)
    (h14852 : p7 ∨ (¬ p124) ∨ (¬ p344) ∨ (¬ p657) ∨ p658 ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p124) ∨ (¬ p344) ∨ (¬ p657) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p658) := by
    exact h16199
  have u6 : p1386 := by
    exact h8348
  rcases h14852 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19465 (p7 p16 p124 p344 p498 p728 p1330 p1349 p1489 : Prop)
    (h16152 : (¬ p7))
    (h14853 : p7 ∨ (¬ p16) ∨ (¬ p124) ∨ (¬ p344) ∨ (¬ p498) ∨ (¬ p728) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p1489)) : (¬ p16) ∨ (¬ p124) ∨ (¬ p344) ∨ (¬ p498) ∨ (¬ p728) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p1489) := by
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
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p498 := by
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
  rcases h14853 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19466 (p7 p43 p71 p495 p577 p1140 p1141 : Prop)
    (h16152 : (¬ p7))
    (h14854 : p7 ∨ (¬ p43) ∨ (¬ p71) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1140) ∨ (¬ p1141)) : (¬ p43) ∨ (¬ p71) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1140) ∨ (¬ p1141) := by
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
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14854 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19467 (p7 p88 p134 p163 p188 p226 p257 p495 p577 p1095 p1096 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h6761 : p1139)
    (h14855 : p7 ∨ (¬ p88) ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ p257 ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1139)) : (¬ p88) ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1095) ∨ (¬ p1096) := by
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
  have u2 : p163 := by
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
  have u5 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p257) := by
    exact h16170
  have u11 : p1139 := by
    exact h6761
  rcases h14855 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
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
  · exact False.elim (q10 u8)
  · exact False.elim (q11 u11)

theorem step19468 (p7 p12 p43 p134 p163 p257 p792 p879 p1074 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h4535 : p792)
    (h14856 : p7 ∨ (¬ p12) ∨ (¬ p43) ∨ (¬ p134) ∨ (¬ p163) ∨ p257 ∨ (¬ p792) ∨ (¬ p879) ∨ (¬ p1074)) : (¬ p12) ∨ (¬ p43) ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p879) ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p879 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p257) := by
    exact h16170
  have u8 : p792 := by
    exact h4535
  rcases h14856 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u7 q5)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step19469 (p7 p43 p167 p495 p577 p882 p1096 p1141 p1256 : Prop)
    (h16152 : (¬ p7))
    (h14857 : p7 ∨ (¬ p43) ∨ (¬ p167) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p882) ∨ (¬ p1096) ∨ (¬ p1141) ∨ (¬ p1256)) : (¬ p43) ∨ (¬ p167) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p882) ∨ (¬ p1096) ∨ (¬ p1141) ∨ (¬ p1256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p167 := by
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
  have u4 : p882 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1096 := by
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
  rcases h14857 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19470 (p7 p124 p134 p208 p257 p344 p657 p1135 p1159 p1256 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h6744 : p1135)
    (h14858 : p7 ∨ (¬ p124) ∨ (¬ p134) ∨ (¬ p208) ∨ p257 ∨ (¬ p344) ∨ (¬ p657) ∨ (¬ p1135) ∨ (¬ p1159) ∨ (¬ p1256)) : (¬ p124) ∨ (¬ p134) ∨ (¬ p208) ∨ (¬ p344) ∨ (¬ p657) ∨ (¬ p1159) ∨ (¬ p1256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p208 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p657 := by
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
  have u8 : (¬ p257) := by
    exact h16170
  have u9 : p1135 := by
    exact h6744
  rcases h14858 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u8 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)

theorem step19472 (p7 p162 p840 p897 p980 p1139 p1225 p1311 : Prop)
    (h16152 : (¬ p7))
    (h16160 : (¬ p162))
    (h6761 : p1139)
    (h14860 : p7 ∨ p162 ∨ (¬ p840) ∨ (¬ p897) ∨ (¬ p980) ∨ (¬ p1139) ∨ (¬ p1225) ∨ (¬ p1311)) : (¬ p840) ∨ (¬ p897) ∨ (¬ p980) ∨ (¬ p1225) ∨ (¬ p1311) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p840 := by
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
  have u6 : (¬ p162) := by
    exact h16160
  have u7 : p1139 := by
    exact h6761
  rcases h14860 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step19473 (p7 p8 p41 p83 p189 p290 p346 p918 p1100 : Prop)
    (h16152 : (¬ p7))
    (h14862 : p7 ∨ (¬ p8) ∨ (¬ p41) ∨ (¬ p83) ∨ (¬ p189) ∨ (¬ p290) ∨ (¬ p346) ∨ (¬ p918) ∨ (¬ p1100)) : (¬ p8) ∨ (¬ p41) ∨ (¬ p83) ∨ (¬ p189) ∨ (¬ p290) ∨ (¬ p346) ∨ (¬ p918) ∨ (¬ p1100) := by
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
  have u4 : p290 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1100 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14862 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19474 (p7 p12 p225 p426 p1074 p1099 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h7053 : p1184)
    (h14863 : p7 ∨ (¬ p12) ∨ (¬ p225) ∨ p426 ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1184)) : (¬ p12) ∨ (¬ p225) ∨ (¬ p1074) ∨ (¬ p1099) := by
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
  have u2 : p1074 := by
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
  rcases h14863 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19475 (p7 p189 p263 p362 p422 p434 p1330 p1465 : Prop)
    (h16152 : (¬ p7))
    (h14864 : p7 ∨ (¬ p189) ∨ (¬ p263) ∨ (¬ p362) ∨ (¬ p422) ∨ (¬ p434) ∨ (¬ p1330) ∨ (¬ p1465)) : (¬ p189) ∨ (¬ p263) ∨ (¬ p362) ∨ (¬ p422) ∨ (¬ p434) ∨ (¬ p1330) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p263 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p434 := by
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
  rcases h14864 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19476 (p7 p87 p185 p262 p362 p434 p544 p581 p653 p685 p836 : Prop)
    (h16152 : (¬ p7))
    (h16194 : (¬ p653))
    (h3898 : p685)
    (h14865 : p7 ∨ (¬ p87) ∨ (¬ p185) ∨ (¬ p262) ∨ (¬ p362) ∨ (¬ p434) ∨ (¬ p544) ∨ (¬ p581) ∨ p653 ∨ (¬ p685) ∨ (¬ p836)) : (¬ p87) ∨ (¬ p185) ∨ (¬ p262) ∨ (¬ p362) ∨ (¬ p434) ∨ (¬ p544) ∨ (¬ p581) ∨ (¬ p836) := by
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
  have u3 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p434 := by
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
  have u7 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p653) := by
    exact h16194
  have u10 : p685 := by
    exact h3898
  rcases h14865 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19477 (p7 p8 p63 p69 p110 p229 p310 p346 p421 p577 : Prop)
    (h16152 : (¬ p7))
    (h14866 : p7 ∨ (¬ p8) ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p110) ∨ (¬ p229) ∨ (¬ p310) ∨ (¬ p346) ∨ (¬ p421) ∨ (¬ p577)) : (¬ p8) ∨ (¬ p63) ∨ (¬ p69) ∨ (¬ p110) ∨ (¬ p229) ∨ (¬ p310) ∨ (¬ p346) ∨ (¬ p421) ∨ (¬ p577) := by
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
  have u2 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14866 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19478 (p4 p7 p387 p544 p669 p1036 : Prop)
    (h16152 : (¬ p7))
    (h14867 : (¬ p4) ∨ p7 ∨ (¬ p387) ∨ (¬ p544) ∨ (¬ p669) ∨ (¬ p1036)) : (¬ p4) ∨ (¬ p387) ∨ (¬ p544) ∨ (¬ p669) ∨ (¬ p1036) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p544 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14867 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19479 (p7 p85 p362 p387 p496 p669 p918 p1115 : Prop)
    (h16152 : (¬ p7))
    (h14868 : p7 ∨ (¬ p85) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p496) ∨ (¬ p669) ∨ (¬ p918) ∨ (¬ p1115)) : (¬ p85) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p496) ∨ (¬ p669) ∨ (¬ p918) ∨ (¬ p1115) := by
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
  have u2 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14868 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19480 (p7 p88 p134 p163 p188 p226 p257 p387 p495 p577 p595 p596 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h6744 : p1135)
    (h14869 : p7 ∨ (¬ p88) ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ p257 ∨ (¬ p387) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p595) ∨ (¬ p596) ∨ (¬ p1135)) : (¬ p88) ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p387) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p595) ∨ (¬ p596) := by
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
  have u2 : p163 := by
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
  have u5 : p387 := by
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
  have u8 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p596 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  have u11 : (¬ p257) := by
    exact h16170
  have u12 : p1135 := by
    exact h6744
  rcases h14869 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
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
  · exact False.elim (q10 u8)
  · exact False.elim (q11 u9)
  · exact False.elim (q12 u12)

theorem step19481 (p7 p185 p263 p362 p434 p980 p1115 p1330 : Prop)
    (h16152 : (¬ p7))
    (h14870 : p7 ∨ (¬ p185) ∨ (¬ p263) ∨ (¬ p362) ∨ (¬ p434) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p1330)) : (¬ p185) ∨ (¬ p263) ∨ (¬ p362) ∨ (¬ p434) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p1330) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p263 := by
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
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14870 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19482 (p7 p88 p134 p163 p188 p226 p257 p495 p577 p1225 p1229 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h8348 : p1386)
    (h14871 : p7 ∨ (¬ p88) ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ p257 ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1386)) : (¬ p88) ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1225) ∨ (¬ p1229) := by
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
  have u2 : p163 := by
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
  have u5 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p257) := by
    exact h16170
  have u11 : p1386 := by
    exact h8348
  rcases h14871 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
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
  · exact False.elim (q10 u8)
  · exact False.elim (q11 u11)

theorem step19483 (p7 p88 p189 p387 p422 p495 p577 p595 p596 p1004 : Prop)
    (h16152 : (¬ p7))
    (h14872 : p7 ∨ (¬ p88) ∨ (¬ p189) ∨ (¬ p387) ∨ (¬ p422) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p595) ∨ (¬ p596) ∨ (¬ p1004)) : (¬ p88) ∨ (¬ p189) ∨ (¬ p387) ∨ (¬ p422) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p595) ∨ (¬ p596) ∨ (¬ p1004) := by
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
  have u2 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p596 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14872 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19484 (p7 p8 p43 p110 p167 p310 p346 p421 p577 p1141 p1256 : Prop)
    (h16152 : (¬ p7))
    (h14873 : p7 ∨ (¬ p8) ∨ (¬ p43) ∨ (¬ p110) ∨ (¬ p167) ∨ (¬ p310) ∨ (¬ p346) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p1141) ∨ (¬ p1256)) : (¬ p8) ∨ (¬ p43) ∨ (¬ p110) ∨ (¬ p167) ∨ (¬ p310) ∨ (¬ p346) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p1141) ∨ (¬ p1256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p43 := by
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
  have u4 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h14873 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19485 (p7 p12 p88 p225 p238 p347 p438 p1055 p1389 p1542 : Prop)
    (h16152 : (¬ p7))
    (h14874 : p7 ∨ (¬ p12) ∨ (¬ p88) ∨ (¬ p225) ∨ (¬ p238) ∨ (¬ p347) ∨ (¬ p438) ∨ (¬ p1055) ∨ (¬ p1389) ∨ (¬ p1542)) : (¬ p12) ∨ (¬ p88) ∨ (¬ p225) ∨ (¬ p238) ∨ (¬ p347) ∨ (¬ p438) ∨ (¬ p1055) ∨ (¬ p1389) ∨ (¬ p1542) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14874 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19486 (p7 p88 p167 p189 p225 p426 p495 p577 p1225 p1229 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h8348 : p1386)
    (h14875 : p7 ∨ (¬ p88) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p225) ∨ p426 ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1386)) : (¬ p88) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p225) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1225) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p88 := by
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
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p577 := by
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
  rcases h14875 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19487 (p7 p8 p45 p85 p134 p257 p346 p1077 p1100 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h6761 : p1139)
    (h14876 : p7 ∨ (¬ p8) ∨ (¬ p45) ∨ (¬ p85) ∨ (¬ p134) ∨ p257 ∨ (¬ p346) ∨ (¬ p1077) ∨ (¬ p1100) ∨ (¬ p1139)) : (¬ p8) ∨ (¬ p45) ∨ (¬ p85) ∨ (¬ p134) ∨ (¬ p346) ∨ (¬ p1077) ∨ (¬ p1100) := by
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
  have u4 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1100 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p257) := by
    exact h16170
  have u9 : p1139 := by
    exact h6761
  rcases h14876 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19488 (p7 p45 p85 p422 p710 p904 p919 p1044 p1061 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16230 : (¬ p919))
    (h7053 : p1184)
    (h14878 : p7 ∨ (¬ p45) ∨ (¬ p85) ∨ (¬ p422) ∨ (¬ p710) ∨ (¬ p904) ∨ p919 ∨ (¬ p1044) ∨ (¬ p1061) ∨ (¬ p1184)) : (¬ p45) ∨ (¬ p85) ∨ (¬ p422) ∨ (¬ p710) ∨ (¬ p904) ∨ (¬ p1044) ∨ (¬ p1061) := by
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
  have u2 : p422 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p919) := by
    exact h16230
  have u9 : p1184 := by
    exact h7053
  rcases h14878 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19489 (p7 p8 p346 p682 p983 p1077 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16203 : (¬ p682))
    (h8348 : p1386)
    (h14879 : p7 ∨ (¬ p8) ∨ (¬ p346) ∨ p682 ∨ (¬ p983) ∨ (¬ p1077) ∨ (¬ p1386)) : (¬ p8) ∨ (¬ p346) ∨ (¬ p983) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p346 := by
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
  have u5 : (¬ p682) := by
    exact h16203
  have u6 : p1386 := by
    exact h8348
  rcases h14879 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19490 (p7 p124 p138 p185 p193 p262 p668 p836 p1077 : Prop)
    (h16152 : (¬ p7))
    (h14880 : p7 ∨ (¬ p124) ∨ (¬ p138) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p262) ∨ (¬ p668) ∨ (¬ p836) ∨ (¬ p1077)) : (¬ p124) ∨ (¬ p138) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p262) ∨ (¬ p668) ∨ (¬ p836) ∨ (¬ p1077) := by
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
  have u5 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14880 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19491 (p7 p12 p126 p194 p225 p256 p387 p426 p556 p1055 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h6744 : p1135)
    (h14881 : p7 ∨ (¬ p12) ∨ (¬ p126) ∨ (¬ p194) ∨ (¬ p225) ∨ (¬ p256) ∨ (¬ p387) ∨ p426 ∨ (¬ p556) ∨ (¬ p1055) ∨ (¬ p1135)) : (¬ p12) ∨ (¬ p126) ∨ (¬ p194) ∨ (¬ p225) ∨ (¬ p256) ∨ (¬ p387) ∨ (¬ p556) ∨ (¬ p1055) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p426) := by
    exact h16178
  have u10 : p1135 := by
    exact h6744
  rcases h14881 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19492 (p7 p12 p110 p194 p266 p288 p301 p362 p556 p1055 : Prop)
    (h16152 : (¬ p7))
    (h14882 : p7 ∨ (¬ p12) ∨ (¬ p110) ∨ (¬ p194) ∨ (¬ p266) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p362) ∨ (¬ p556) ∨ (¬ p1055)) : (¬ p12) ∨ (¬ p110) ∨ (¬ p194) ∨ (¬ p266) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p362) ∨ (¬ p556) ∨ (¬ p1055) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p266 := by
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
  have u6 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14882 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19493 (p7 p14 p64 p226 p387 p438 p617 p687 p875 p1135 p1187 : Prop)
    (h16152 : (¬ p7))
    (h16220 : (¬ p875))
    (h6744 : p1135)
    (h14883 : p7 ∨ (¬ p14) ∨ (¬ p64) ∨ (¬ p226) ∨ (¬ p387) ∨ (¬ p438) ∨ (¬ p617) ∨ (¬ p687) ∨ p875 ∨ (¬ p1135) ∨ (¬ p1187)) : (¬ p14) ∨ (¬ p64) ∨ (¬ p226) ∨ (¬ p387) ∨ (¬ p438) ∨ (¬ p617) ∨ (¬ p687) ∨ (¬ p1187) := by
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
  have u2 : p226 := by
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
  have u5 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p875) := by
    exact h16220
  have u10 : p1135 := by
    exact h6744
  rcases h14883 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19494 (p7 p17 p230 p581 p789 p790 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6744 : p1135)
    (h14884 : p7 ∨ (¬ p17) ∨ p230 ∨ (¬ p581) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1135)) : (¬ p17) ∨ (¬ p581) ∨ (¬ p789) ∨ (¬ p790) := by
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
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p1135 := by
    exact h6744
  rcases h14884 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19495 (p7 p14 p64 p226 p362 p387 p496 p1004 p1141 : Prop)
    (h16152 : (¬ p7))
    (h14885 : p7 ∨ (¬ p14) ∨ (¬ p64) ∨ (¬ p226) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p496) ∨ (¬ p1004) ∨ (¬ p1141)) : (¬ p14) ∨ (¬ p64) ∨ (¬ p226) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p496) ∨ (¬ p1004) ∨ (¬ p1141) := by
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
  have u2 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p496 := by
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
  rcases h14885 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19496 (p7 p17 p230 p387 p518 p581 p790 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6744 : p1135)
    (h14886 : p7 ∨ (¬ p17) ∨ p230 ∨ (¬ p387) ∨ (¬ p518) ∨ (¬ p581) ∨ (¬ p790) ∨ (¬ p1135)) : (¬ p17) ∨ (¬ p387) ∨ (¬ p518) ∨ (¬ p581) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p387 := by
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
  have u4 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p1135 := by
    exact h6744
  rcases h14886 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step19497 (p7 p17 p123 p387 p518 p790 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h8348 : p1386)
    (h14888 : p7 ∨ (¬ p17) ∨ p123 ∨ (¬ p387) ∨ (¬ p518) ∨ (¬ p790) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p17) ∨ (¬ p387) ∨ (¬ p518) ∨ (¬ p790) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p518 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p123) := by
    exact h16186
  have u7 : p1386 := by
    exact h8348
  rcases h14888 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step19498 (p7 p69 p229 p362 p387 p496 p669 p1036 : Prop)
    (h16152 : (¬ p7))
    (h14889 : p7 ∨ (¬ p69) ∨ (¬ p229) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p496) ∨ (¬ p669) ∨ (¬ p1036)) : (¬ p69) ∨ (¬ p229) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p496) ∨ (¬ p669) ∨ (¬ p1036) := by
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
  have u2 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14889 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19500 (p7 p8 p129 p142 p207 p310 p346 p1077 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h6761 : p1139)
    (h14891 : p7 ∨ (¬ p8) ∨ p129 ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p310) ∨ (¬ p346) ∨ (¬ p1077) ∨ (¬ p1139)) : (¬ p8) ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p310) ∨ (¬ p346) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
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
  have u3 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p129) := by
    exact h16154
  have u8 : p1139 := by
    exact h6761
  rcases h14891 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u8)

theorem step19501 (p7 p124 p142 p191 p207 p225 p226 p668 p1077 : Prop)
    (h16152 : (¬ p7))
    (h14892 : p7 ∨ (¬ p124) ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p207) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p668) ∨ (¬ p1077)) : (¬ p124) ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p207) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p668) ∨ (¬ p1077) := by
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
  have u2 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14892 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19502 (p7 p45 p85 p124 p134 p257 p344 p496 p657 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h6744 : p1135)
    (h14894 : p7 ∨ (¬ p45) ∨ (¬ p85) ∨ (¬ p124) ∨ (¬ p134) ∨ p257 ∨ (¬ p344) ∨ (¬ p496) ∨ (¬ p657) ∨ (¬ p1135)) : (¬ p45) ∨ (¬ p85) ∨ (¬ p124) ∨ (¬ p134) ∨ (¬ p344) ∨ (¬ p496) ∨ (¬ p657) := by
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
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
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
  have u6 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p257) := by
    exact h16170
  have u9 : p1135 := by
    exact h6744
  rcases h14894 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19503 (p7 p41 p83 p123 p124 p189 p344 p496 p576 p657 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h6744 : p1135)
    (h14895 : p7 ∨ (¬ p41) ∨ (¬ p83) ∨ p123 ∨ (¬ p124) ∨ (¬ p189) ∨ (¬ p344) ∨ (¬ p496) ∨ (¬ p576) ∨ (¬ p657) ∨ (¬ p1135)) : (¬ p41) ∨ (¬ p83) ∨ (¬ p124) ∨ (¬ p189) ∨ (¬ p344) ∨ (¬ p496) ∨ (¬ p576) ∨ (¬ p657) := by
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
  have u6 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p123) := by
    exact h16186
  have u10 : p1135 := by
    exact h6744
  rcases h14895 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19504 (p7 p84 p124 p258 p266 p1035 p1214 p1226 p1235 p1274 p1443 : Prop)
    (h16152 : (¬ p7))
    (h14896 : p7 ∨ (¬ p84) ∨ (¬ p124) ∨ (¬ p258) ∨ (¬ p266) ∨ (¬ p1035) ∨ (¬ p1214) ∨ (¬ p1226) ∨ (¬ p1235) ∨ (¬ p1274) ∨ (¬ p1443)) : (¬ p84) ∨ (¬ p124) ∨ (¬ p258) ∨ (¬ p266) ∨ (¬ p1035) ∨ (¬ p1214) ∨ (¬ p1226) ∨ (¬ p1235) ∨ (¬ p1274) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1214 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1235 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1274 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h14896 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19505 (p7 p362 p434 p657 p658 p734 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16199 : (¬ p658))
    (h6744 : p1135)
    (h14897 : p7 ∨ (¬ p362) ∨ (¬ p434) ∨ (¬ p657) ∨ p658 ∨ (¬ p734) ∨ (¬ p1135)) : (¬ p362) ∨ (¬ p434) ∨ (¬ p657) ∨ (¬ p734) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p658) := by
    exact h16199
  have u6 : p1135 := by
    exact h6744
  rcases h14897 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19507 (p7 p15 p22 p124 p126 p258 p421 p603 p616 : Prop)
    (h16152 : (¬ p7))
    (h14899 : p7 ∨ (¬ p15) ∨ (¬ p22) ∨ (¬ p124) ∨ (¬ p126) ∨ (¬ p258) ∨ (¬ p421) ∨ (¬ p603) ∨ (¬ p616)) : (¬ p15) ∨ (¬ p22) ∨ (¬ p124) ∨ (¬ p126) ∨ (¬ p258) ∨ (¬ p421) ∨ (¬ p603) ∨ (¬ p616) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p22 := by
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
  have u5 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p603 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14899 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19508 (p7 p124 p161 p344 p496 p728 p1232 p1330 : Prop)
    (h16152 : (¬ p7))
    (h14900 : p7 ∨ (¬ p124) ∨ (¬ p161) ∨ (¬ p344) ∨ (¬ p496) ∨ (¬ p728) ∨ (¬ p1232) ∨ (¬ p1330)) : (¬ p124) ∨ (¬ p161) ∨ (¬ p344) ∨ (¬ p496) ∨ (¬ p728) ∨ (¬ p1232) ∨ (¬ p1330) := by
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
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p496 := by
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
  rcases h14900 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19509 (p7 p124 p194 p266 p344 p728 p1159 p1330 p1465 : Prop)
    (h16152 : (¬ p7))
    (h14901 : p7 ∨ (¬ p124) ∨ (¬ p194) ∨ (¬ p266) ∨ (¬ p344) ∨ (¬ p728) ∨ (¬ p1159) ∨ (¬ p1330) ∨ (¬ p1465)) : (¬ p124) ∨ (¬ p194) ∨ (¬ p266) ∨ (¬ p344) ∨ (¬ p728) ∨ (¬ p1159) ∨ (¬ p1330) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14901 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19510 (p7 p123 p224 p288 p343 p383 p455 p636 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h1950 : p343)
    (h14902 : p7 ∨ p123 ∨ (¬ p224) ∨ (¬ p288) ∨ (¬ p343) ∨ (¬ p383) ∨ (¬ p455) ∨ (¬ p636)) : (¬ p224) ∨ (¬ p288) ∨ (¬ p383) ∨ (¬ p455) ∨ (¬ p636) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p383 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p123) := by
    exact h16186
  have u7 : p343 := by
    exact h1950
  rcases h14902 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step19511 (p7 p129 p142 p207 p224 p343 p362 p387 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h1950 : p343)
    (h14903 : p7 ∨ p129 ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p224) ∨ (¬ p343) ∨ (¬ p362) ∨ (¬ p387)) : (¬ p142) ∨ (¬ p207) ∨ (¬ p224) ∨ (¬ p362) ∨ (¬ p387) := by
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
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p343 := by
    exact h1950
  rcases h14903 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step19512 (p7 p43 p134 p224 p257 p343 p362 p387 p421 p577 p1141 p1256 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h1950 : p343)
    (h14904 : p7 ∨ (¬ p43) ∨ (¬ p134) ∨ (¬ p224) ∨ p257 ∨ (¬ p343) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p1141) ∨ (¬ p1256)) : (¬ p43) ∨ (¬ p134) ∨ (¬ p224) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p1141) ∨ (¬ p1256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p387 := by
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
  have u7 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p257) := by
    exact h16170
  have u11 : p343 := by
    exact h1950
  rcases h14904 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u10 q4)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step19513 (p7 p69 p224 p362 p387 p496 p545 p1187 : Prop)
    (h16152 : (¬ p7))
    (h14905 : p7 ∨ (¬ p69) ∨ (¬ p224) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p496) ∨ (¬ p545) ∨ (¬ p1187)) : (¬ p69) ∨ (¬ p224) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p496) ∨ (¬ p545) ∨ (¬ p1187) := by
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
  have u2 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p387 := by
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
  have u6 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14905 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19514 (p7 p189 p224 p263 p362 p387 p422 p545 p1002 : Prop)
    (h16152 : (¬ p7))
    (h14906 : p7 ∨ (¬ p189) ∨ (¬ p224) ∨ (¬ p263) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p422) ∨ (¬ p545) ∨ (¬ p1002)) : (¬ p189) ∨ (¬ p224) ∨ (¬ p263) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p422) ∨ (¬ p545) ∨ (¬ p1002) := by
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
  have u2 : p263 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1002 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14906 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19515 (p7 p45 p193 p224 p362 p387 p545 p658 p792 p798 p814 : Prop)
    (h16152 : (¬ p7))
    (h16199 : (¬ p658))
    (h4535 : p792)
    (h14907 : p7 ∨ (¬ p45) ∨ (¬ p193) ∨ (¬ p224) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p545) ∨ p658 ∨ (¬ p792) ∨ (¬ p798) ∨ (¬ p814)) : (¬ p45) ∨ (¬ p193) ∨ (¬ p224) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p545) ∨ (¬ p798) ∨ (¬ p814) := by
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
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p798 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p658) := by
    exact h16199
  have u10 : p792 := by
    exact h4535
  rcases h14907 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19516 (p7 p69 p225 p229 p344 p686 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h7053 : p1184)
    (h14908 : p7 ∨ (¬ p69) ∨ (¬ p225) ∨ (¬ p229) ∨ (¬ p344) ∨ p686 ∨ (¬ p1184)) : (¬ p69) ∨ (¬ p225) ∨ (¬ p229) ∨ (¬ p344) := by
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
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p686) := by
    exact h16205
  have u6 : p1184 := by
    exact h7053
  rcases h14908 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step19517 (p6 p7 p104 p142 p167 p659 p1076 p1181 : Prop)
    (h16152 : (¬ p7))
    (h3753 : p659)
    (h16272 : (¬ p1181))
    (h14909 : (¬ p6) ∨ p7 ∨ (¬ p104) ∨ (¬ p142) ∨ (¬ p167) ∨ (¬ p659) ∨ (¬ p1076) ∨ p1181) : (¬ p6) ∨ (¬ p104) ∨ (¬ p142) ∨ (¬ p167) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
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
  have u3 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p659 := by
    exact h3753
  have u7 : (¬ p1181) := by
    exact h16272
  rcases h14909 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step19518 (p7 p20 p46 p102 p142 p304 p425 : Prop)
    (h16152 : (¬ p7))
    (h14911 : p7 ∨ (¬ p20) ∨ (¬ p46) ∨ (¬ p102) ∨ (¬ p142) ∨ (¬ p304) ∨ (¬ p425)) : (¬ p20) ∨ (¬ p46) ∨ (¬ p102) ∨ (¬ p142) ∨ (¬ p304) ∨ (¬ p425) := by
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
  have u2 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14911 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19519 (p7 p280 p304 p387 p594 p633 p681 p1287 : Prop)
    (h16152 : (¬ p7))
    (h16173 : (¬ p280))
    (h3892 : p681)
    (h14912 : p7 ∨ p280 ∨ (¬ p304) ∨ (¬ p387) ∨ (¬ p594) ∨ (¬ p633) ∨ (¬ p681) ∨ (¬ p1287)) : (¬ p304) ∨ (¬ p387) ∨ (¬ p594) ∨ (¬ p633) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p594 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p280) := by
    exact h16173
  have u7 : p681 := by
    exact h3892
  rcases h14912 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step19520 (p6 p7 p101 p280 p288 p301 p659 : Prop)
    (h16152 : (¬ p7))
    (h16173 : (¬ p280))
    (h3753 : p659)
    (h14913 : (¬ p6) ∨ p7 ∨ (¬ p101) ∨ p280 ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p659)) : (¬ p6) ∨ (¬ p101) ∨ (¬ p288) ∨ (¬ p301) := by
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
  have u2 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p280) := by
    exact h16173
  have u6 : p659 := by
    exact h3753
  rcases h14913 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19521 (p7 p17 p258 p279 p980 p1076 p1324 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16309 : (¬ p1324))
    (h14914 : p7 ∨ (¬ p17) ∨ (¬ p258) ∨ (¬ p279) ∨ (¬ p980) ∨ (¬ p1076) ∨ p1324) : (¬ p17) ∨ (¬ p258) ∨ (¬ p980) ∨ (¬ p1076) := by
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
  have u5 : p279 := by
    exact h1444
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h14914 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step19522 (p7 p163 p188 p226 p406 p796 p817 p1191 p1287 : Prop)
    (h16152 : (¬ p7))
    (h14915 : p7 ∨ (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p406) ∨ (¬ p796) ∨ (¬ p817) ∨ (¬ p1191) ∨ (¬ p1287)) : (¬ p163) ∨ (¬ p188) ∨ (¬ p226) ∨ (¬ p406) ∨ (¬ p796) ∨ (¬ p817) ∨ (¬ p1191) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p817 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14915 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19523 (p7 p17 p88 p258 p616 p1076 p1229 p1309 p1389 : Prop)
    (h16152 : (¬ p7))
    (h14916 : p7 ∨ (¬ p17) ∨ (¬ p88) ∨ (¬ p258) ∨ (¬ p616) ∨ (¬ p1076) ∨ (¬ p1229) ∨ (¬ p1309) ∨ (¬ p1389)) : (¬ p17) ∨ (¬ p88) ∨ (¬ p258) ∨ (¬ p616) ∨ (¬ p1076) ∨ (¬ p1229) ∨ (¬ p1309) ∨ (¬ p1389) := by
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
  have u2 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14916 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19524 (p6 p7 p142 p160 p188 p422 p669 p1038 p1325 p1350 : Prop)
    (h16152 : (¬ p7))
    (h14917 : (¬ p6) ∨ p7 ∨ (¬ p142) ∨ (¬ p160) ∨ (¬ p188) ∨ (¬ p422) ∨ (¬ p669) ∨ (¬ p1038) ∨ (¬ p1325) ∨ (¬ p1350)) : (¬ p6) ∨ (¬ p142) ∨ (¬ p160) ∨ (¬ p188) ∨ (¬ p422) ∨ (¬ p669) ∨ (¬ p1038) ∨ (¬ p1325) ∨ (¬ p1350) := by
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
  have u2 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1038 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14917 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19525 (p6 p7 p101 p188 p406 p726 p817 p985 p1333 : Prop)
    (h16152 : (¬ p7))
    (h14918 : (¬ p6) ∨ p7 ∨ (¬ p101) ∨ (¬ p188) ∨ (¬ p406) ∨ (¬ p726) ∨ (¬ p817) ∨ (¬ p985) ∨ (¬ p1333)) : (¬ p6) ∨ (¬ p101) ∨ (¬ p188) ∨ (¬ p406) ∨ (¬ p726) ∨ (¬ p817) ∨ (¬ p985) ∨ (¬ p1333) := by
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
  have u2 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p817 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14918 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19526 (p3 p6 p7 p10 p107 p342 : Prop)
    (h16152 : (¬ p7))
    (h14920 : (¬ p3) ∨ (¬ p6) ∨ p7 ∨ (¬ p10) ∨ (¬ p107) ∨ (¬ p342)) : (¬ p3) ∨ (¬ p6) ∨ (¬ p10) ∨ (¬ p107) ∨ (¬ p342) := by
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
  have u2 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p342 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14920 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19527 (p7 p124 p125 p129 p142 p323 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h6478 : p1075)
    (h14921 : p7 ∨ (¬ p124) ∨ (¬ p125) ∨ p129 ∨ (¬ p142) ∨ (¬ p323) ∨ (¬ p1075)) : (¬ p124) ∨ (¬ p125) ∨ (¬ p142) ∨ (¬ p323) := by
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
  have u2 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p1075 := by
    exact h6478
  rcases h14921 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19528 (p7 p12 p108 p142 p191 p556 p1055 : Prop)
    (h16152 : (¬ p7))
    (h14922 : p7 ∨ (¬ p12) ∨ (¬ p108) ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p556) ∨ (¬ p1055)) : (¬ p12) ∨ (¬ p108) ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p556) ∨ (¬ p1055) := by
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
  have u2 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14922 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19529 (p4 p7 p124 p125 p738 p756 : Prop)
    (h16152 : (¬ p7))
    (h14924 : (¬ p4) ∨ p7 ∨ (¬ p124) ∨ (¬ p125) ∨ (¬ p738) ∨ (¬ p756)) : (¬ p4) ∨ (¬ p124) ∨ (¬ p125) ∨ (¬ p738) ∨ (¬ p756) := by
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
  rcases h14924 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19530 (p7 p191 p226 p406 p424 p476 p940 p985 p1333 : Prop)
    (h16152 : (¬ p7))
    (h14925 : p7 ∨ (¬ p191) ∨ (¬ p226) ∨ (¬ p406) ∨ (¬ p424) ∨ (¬ p476) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1333)) : (¬ p191) ∨ (¬ p226) ∨ (¬ p406) ∨ (¬ p424) ∨ (¬ p476) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p476 := by
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
  have u7 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h14925 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19531 (p6 p7 p10 p126 p141 p191 : Prop)
    (h16152 : (¬ p7))
    (h14926 : (¬ p6) ∨ p7 ∨ (¬ p10) ∨ (¬ p126) ∨ (¬ p141) ∨ (¬ p191)) : (¬ p6) ∨ (¬ p10) ∨ (¬ p126) ∨ (¬ p141) ∨ (¬ p191) := by
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
  have u2 : p126 := by
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
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14926 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19532 (p7 p191 p226 p405 p424 p476 p669 p1036 p1225 p1235 p1325 : Prop)
    (h16152 : (¬ p7))
    (h14927 : p7 ∨ (¬ p191) ∨ (¬ p226) ∨ (¬ p405) ∨ (¬ p424) ∨ (¬ p476) ∨ (¬ p669) ∨ (¬ p1036) ∨ (¬ p1225) ∨ (¬ p1235) ∨ (¬ p1325)) : (¬ p191) ∨ (¬ p226) ∨ (¬ p405) ∨ (¬ p424) ∨ (¬ p476) ∨ (¬ p669) ∨ (¬ p1036) ∨ (¬ p1225) ∨ (¬ p1235) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p405 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p476 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1235 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h14927 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19533 (p7 p16 p17 p301 p431 p438 p595 p1286 : Prop)
    (h16152 : (¬ p7))
    (h14928 : p7 ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p301) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p595) ∨ (¬ p1286)) : (¬ p16) ∨ (¬ p17) ∨ (¬ p301) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p595) ∨ (¬ p1286) := by
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
  have u2 : p301 := by
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
  rcases h14928 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19534 (p5 p7 p595 p669 p983 p1159 p1286 p1465 : Prop)
    (h16152 : (¬ p7))
    (h14929 : (¬ p5) ∨ p7 ∨ (¬ p595) ∨ (¬ p669) ∨ (¬ p983) ∨ (¬ p1159) ∨ (¬ p1286) ∨ (¬ p1465)) : (¬ p5) ∨ (¬ p595) ∨ (¬ p669) ∨ (¬ p983) ∨ (¬ p1159) ∨ (¬ p1286) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1159 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14929 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19535 (p7 p38 p46 p169 p226 p424 p476 p687 p980 p1115 p1330 : Prop)
    (h16152 : (¬ p7))
    (h14930 : p7 ∨ (¬ p38) ∨ (¬ p46) ∨ (¬ p169) ∨ (¬ p226) ∨ (¬ p424) ∨ (¬ p476) ∨ (¬ p687) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p1330)) : (¬ p38) ∨ (¬ p46) ∨ (¬ p169) ∨ (¬ p226) ∨ (¬ p424) ∨ (¬ p476) ∨ (¬ p687) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p1330) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p46 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p169 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p226 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h14930 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19537 (p7 p69 p129 p229 p669 p1036 p1142 p1184 p1225 p1256 p1325 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h7053 : p1184)
    (h14932 : p7 ∨ (¬ p69) ∨ p129 ∨ (¬ p229) ∨ (¬ p669) ∨ (¬ p1036) ∨ (¬ p1142) ∨ (¬ p1184) ∨ (¬ p1225) ∨ (¬ p1256) ∨ (¬ p1325)) : (¬ p69) ∨ (¬ p229) ∨ (¬ p669) ∨ (¬ p1036) ∨ (¬ p1142) ∨ (¬ p1225) ∨ (¬ p1256) ∨ (¬ p1325) := by
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
  have u2 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p129) := by
    exact h16154
  have u10 : p1184 := by
    exact h7053
  rcases h14932 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19538 (p6 p7 p142 p344 p540 p659 p686 p796 : Prop)
    (h16152 : (¬ p7))
    (h3753 : p659)
    (h16205 : (¬ p686))
    (h14934 : (¬ p6) ∨ p7 ∨ (¬ p142) ∨ (¬ p344) ∨ (¬ p540) ∨ (¬ p659) ∨ p686 ∨ (¬ p796)) : (¬ p6) ∨ (¬ p142) ∨ (¬ p344) ∨ (¬ p540) ∨ (¬ p796) := by
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
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p659 := by
    exact h3753
  have u7 : (¬ p686) := by
    exact h16205
  rcases h14934 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step19539 (p7 p12 p163 p540 p668 p796 : Prop)
    (h16152 : (¬ p7))
    (h14935 : p7 ∨ (¬ p12) ∨ (¬ p163) ∨ (¬ p540) ∨ (¬ p668) ∨ (¬ p796)) : (¬ p12) ∨ (¬ p163) ∨ (¬ p540) ∨ (¬ p668) ∨ (¬ p796) := by
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
  have u2 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14935 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19540 (p7 p163 p544 p657 p796 p875 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16220 : (¬ p875))
    (h6744 : p1135)
    (h14936 : p7 ∨ (¬ p163) ∨ (¬ p544) ∨ (¬ p657) ∨ (¬ p796) ∨ p875 ∨ (¬ p1135)) : (¬ p163) ∨ (¬ p544) ∨ (¬ p657) ∨ (¬ p796) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p875) := by
    exact h16220
  have u6 : p1135 := by
    exact h6744
  rcases h14936 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step19541 (p6 p7 p142 p167 p225 p426 p659 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h3753 : p659)
    (h14937 : (¬ p6) ∨ p7 ∨ (¬ p142) ∨ (¬ p167) ∨ (¬ p225) ∨ p426 ∨ (¬ p659)) : (¬ p6) ∨ (¬ p142) ∨ (¬ p167) ∨ (¬ p225) := by
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
  have u2 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p426) := by
    exact h16178
  have u6 : p659 := by
    exact h3753
  rcases h14937 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step19542 (p6 p7 p8 p142 p167 p188 p239 p653 p657 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16194 : (¬ p653))
    (h8348 : p1386)
    (h14938 : (¬ p6) ∨ p7 ∨ (¬ p8) ∨ (¬ p142) ∨ (¬ p167) ∨ (¬ p188) ∨ (¬ p239) ∨ p653 ∨ (¬ p657) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p6) ∨ (¬ p8) ∨ (¬ p142) ∨ (¬ p167) ∨ (¬ p188) ∨ (¬ p239) ∨ (¬ p657) ∨ (¬ p1333) := by
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
  have u2 : p142 := by
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
  have u5 : p239 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p653) := by
    exact h16194
  have u10 : p1386 := by
    exact h8348
  rcases h14938 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19543 (p7 p544 p657 p882 p898 p1287 : Prop)
    (h16152 : (¬ p7))
    (h14939 : p7 ∨ (¬ p544) ∨ (¬ p657) ∨ (¬ p882) ∨ (¬ p898) ∨ (¬ p1287)) : (¬ p544) ∨ (¬ p657) ∨ (¬ p882) ∨ (¬ p898) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p882 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p898 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14939 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19545 (p7 p8 p11 p85 p389 p576 p657 p1100 : Prop)
    (h16152 : (¬ p7))
    (h14941 : p7 ∨ (¬ p8) ∨ (¬ p11) ∨ (¬ p85) ∨ (¬ p389) ∨ (¬ p576) ∨ (¬ p657) ∨ (¬ p1100)) : (¬ p8) ∨ (¬ p11) ∨ (¬ p85) ∨ (¬ p389) ∨ (¬ p576) ∨ (¬ p657) ∨ (¬ p1100) := by
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
  have u2 : p85 := by
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
  have u6 : p1100 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14941 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19546 (p7 p18 p69 p142 p796 p875 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16220 : (¬ p875))
    (h7053 : p1184)
    (h14942 : p7 ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p142) ∨ (¬ p796) ∨ p875 ∨ (¬ p1184)) : (¬ p18) ∨ (¬ p69) ∨ (¬ p142) ∨ (¬ p796) := by
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
  have u2 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p875) := by
    exact h16220
  have u6 : p1184 := by
    exact h7053
  rcases h14942 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step19547 (p6 p7 p88 p142 p188 p545 p615 p687 p734 p796 p1389 : Prop)
    (h16152 : (¬ p7))
    (h14943 : (¬ p6) ∨ p7 ∨ (¬ p88) ∨ (¬ p142) ∨ (¬ p188) ∨ (¬ p545) ∨ (¬ p615) ∨ (¬ p687) ∨ (¬ p734) ∨ (¬ p796) ∨ (¬ p1389)) : (¬ p6) ∨ (¬ p88) ∨ (¬ p142) ∨ (¬ p188) ∨ (¬ p545) ∨ (¬ p615) ∨ (¬ p687) ∨ (¬ p734) ∨ (¬ p796) ∨ (¬ p1389) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p615 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h14943 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19548 (p7 p8 p11 p17 p239 p532 p728 p1330 : Prop)
    (h16152 : (¬ p7))
    (h14944 : p7 ∨ (¬ p8) ∨ (¬ p11) ∨ (¬ p17) ∨ (¬ p239) ∨ (¬ p532) ∨ (¬ p728) ∨ (¬ p1330)) : (¬ p8) ∨ (¬ p11) ∨ (¬ p17) ∨ (¬ p239) ∨ (¬ p532) ∨ (¬ p728) ∨ (¬ p1330) := by
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
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p239 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14944 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19549 (p7 p167 p559 p1041 p1055 p1256 : Prop)
    (h16152 : (¬ p7))
    (h14945 : p7 ∨ (¬ p167) ∨ (¬ p559) ∨ (¬ p1041) ∨ (¬ p1055) ∨ (¬ p1256)) : (¬ p167) ∨ (¬ p559) ∨ (¬ p1041) ∨ (¬ p1055) ∨ (¬ p1256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p559 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1041 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14945 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19550 (p7 p121 p142 p191 p206 p961 : Prop)
    (h16152 : (¬ p7))
    (h14947 : p7 ∨ (¬ p121) ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p206) ∨ (¬ p961)) : (¬ p121) ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p206) ∨ (¬ p961) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p121 := by
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
  have u4 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14947 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19551 (p7 p167 p653 p1135 p1164 p1225 p1235 p1256 p1325 : Prop)
    (h16152 : (¬ p7))
    (h16194 : (¬ p653))
    (h6744 : p1135)
    (h14948 : p7 ∨ (¬ p167) ∨ p653 ∨ (¬ p1135) ∨ (¬ p1164) ∨ (¬ p1225) ∨ (¬ p1235) ∨ (¬ p1256) ∨ (¬ p1325)) : (¬ p167) ∨ (¬ p1164) ∨ (¬ p1225) ∨ (¬ p1235) ∨ (¬ p1256) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1164 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1235 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p653) := by
    exact h16194
  have u8 : p1135 := by
    exact h6744
  rcases h14948 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u5)

theorem step19552 (p6 p7 p128 p129 p142 p1140 p1141 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16154 : (¬ p129))
    (h14949 : (¬ p6) ∨ p7 ∨ (¬ p128) ∨ p129 ∨ (¬ p142) ∨ (¬ p1140) ∨ (¬ p1141)) : (¬ p6) ∨ (¬ p142) ∨ (¬ p1140) ∨ (¬ p1141) := by
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
  have u3 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p128 := by
    exact h653
  have u6 : (¬ p129) := by
    exact h16154
  rcases h14949 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19553 (p7 p544 p653 p710 p1061 p1074 p1531 : Prop)
    (h16152 : (¬ p7))
    (h16194 : (¬ p653))
    (h9335 : p1531)
    (h14950 : p7 ∨ (¬ p544) ∨ p653 ∨ (¬ p710) ∨ (¬ p1061) ∨ (¬ p1074) ∨ (¬ p1531)) : (¬ p544) ∨ (¬ p710) ∨ (¬ p1061) ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p653) := by
    exact h16194
  have u6 : p1531 := by
    exact h9335
  rcases h14950 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19554 (p7 p544 p656 p687 p882 p898 p1545 : Prop)
    (h16152 : (¬ p7))
    (h14951 : p7 ∨ (¬ p544) ∨ (¬ p656) ∨ (¬ p687) ∨ (¬ p882) ∨ (¬ p898) ∨ (¬ p1545)) : (¬ p544) ∨ (¬ p656) ∨ (¬ p687) ∨ (¬ p882) ∨ (¬ p898) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p656 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p882 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p898 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14951 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19555 (p7 p11 p16 p17 p532 p595 p1330 p1542 : Prop)
    (h16152 : (¬ p7))
    (h14952 : p7 ∨ (¬ p11) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p532) ∨ (¬ p595) ∨ (¬ p1330) ∨ (¬ p1542)) : (¬ p11) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p532) ∨ (¬ p595) ∨ (¬ p1330) ∨ (¬ p1542) := by
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
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p595 := by
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
  rcases h14952 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19557 (p7 p88 p188 p460 p616 p1159 p1229 p1389 p1452 p1465 : Prop)
    (h16152 : (¬ p7))
    (h14954 : p7 ∨ (¬ p88) ∨ (¬ p188) ∨ (¬ p460) ∨ (¬ p616) ∨ (¬ p1159) ∨ (¬ p1229) ∨ (¬ p1389) ∨ (¬ p1452) ∨ (¬ p1465)) : (¬ p88) ∨ (¬ p188) ∨ (¬ p460) ∨ (¬ p616) ∨ (¬ p1159) ∨ (¬ p1229) ∨ (¬ p1389) ∨ (¬ p1452) ∨ (¬ p1465) := by
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
  have u2 : p460 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p616 := by
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
  have u6 : p1389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14954 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19558 (p6 p7 p16 p142 p188 p422 p595 p1004 p1286 : Prop)
    (h16152 : (¬ p7))
    (h14955 : (¬ p6) ∨ p7 ∨ (¬ p16) ∨ (¬ p142) ∨ (¬ p188) ∨ (¬ p422) ∨ (¬ p595) ∨ (¬ p1004) ∨ (¬ p1286)) : (¬ p6) ∨ (¬ p16) ∨ (¬ p142) ∨ (¬ p188) ∨ (¬ p422) ∨ (¬ p595) ∨ (¬ p1004) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p188 := by
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
  rcases h14955 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19559 (p6 p7 p8 p142 p188 p239 p422 p657 p1004 : Prop)
    (h16152 : (¬ p7))
    (h14956 : (¬ p6) ∨ p7 ∨ (¬ p8) ∨ (¬ p142) ∨ (¬ p188) ∨ (¬ p239) ∨ (¬ p422) ∨ (¬ p657) ∨ (¬ p1004)) : (¬ p6) ∨ (¬ p8) ∨ (¬ p142) ∨ (¬ p188) ∨ (¬ p239) ∨ (¬ p422) ∨ (¬ p657) ∨ (¬ p1004) := by
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
  have u2 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p239 := by
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
  rcases h14956 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19560 (p7 p167 p424 p543 p559 p710 : Prop)
    (h16152 : (¬ p7))
    (h14958 : p7 ∨ (¬ p167) ∨ (¬ p424) ∨ (¬ p543) ∨ (¬ p559) ∨ (¬ p710)) : (¬ p167) ∨ (¬ p424) ∨ (¬ p543) ∨ (¬ p559) ∨ (¬ p710) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p543 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p559 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14958 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19561 (p2 p7 p88 p167 p188 p424 p595 p653 p924 p1099 p1135 p1286 : Prop)
    (h16152 : (¬ p7))
    (h16194 : (¬ p653))
    (h6744 : p1135)
    (h14959 : (¬ p2) ∨ p7 ∨ (¬ p88) ∨ (¬ p167) ∨ (¬ p188) ∨ (¬ p424) ∨ (¬ p595) ∨ p653 ∨ (¬ p924) ∨ (¬ p1099) ∨ (¬ p1135) ∨ (¬ p1286)) : (¬ p2) ∨ (¬ p88) ∨ (¬ p167) ∨ (¬ p188) ∨ (¬ p424) ∨ (¬ p595) ∨ (¬ p924) ∨ (¬ p1099) ∨ (¬ p1286) := by
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
  have u2 : p167 := by
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
  have u5 : p595 := by
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
  have u8 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p653) := by
    exact h16194
  have u11 : p1135 := by
    exact h6744
  rcases h14959 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u0)
  · exact False.elim (u9 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u10 q7)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u11)
  · exact False.elim (q11 u8)

theorem step19562 (p642 p919 p1077 p1139 : Prop)
    (h16230 : (¬ p919))
    (h6761 : p1139)
    (h14960 : p642 ∨ p919 ∨ (¬ p1077) ∨ (¬ p1139)) : p642 ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p642) := fun hu => hn (Or.inl hu)
  have u1 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p919) := by
    exact h16230
  have u3 : p1139 := by
    exact h6761
  rcases h14960 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)

theorem step19563 (p7 p11 p13 p85 p344 p576 p686 p710 p1061 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h7053 : p1184)
    (h14962 : p7 ∨ (¬ p11) ∨ (¬ p13) ∨ (¬ p85) ∨ (¬ p344) ∨ (¬ p576) ∨ p686 ∨ (¬ p710) ∨ (¬ p1061) ∨ (¬ p1184)) : (¬ p11) ∨ (¬ p13) ∨ (¬ p85) ∨ (¬ p344) ∨ (¬ p576) ∨ (¬ p710) ∨ (¬ p1061) := by
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
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p686) := by
    exact h16205
  have u9 : p1184 := by
    exact h7053
  rcases h14962 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19564 (p6 p7 p19 p191 p424 p1187 : Prop)
    (h16152 : (¬ p7))
    (h14963 : (¬ p6) ∨ p7 ∨ (¬ p19) ∨ (¬ p191) ∨ (¬ p424) ∨ (¬ p1187)) : (¬ p6) ∨ (¬ p19) ∨ (¬ p191) ∨ (¬ p424) ∨ (¬ p1187) := by
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
  have u2 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14963 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19565 (p7 p123 p124 p125 p126 p1077 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h6761 : p1139)
    (h14964 : p7 ∨ p123 ∨ (¬ p124) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p1077) ∨ (¬ p1139)) : (¬ p124) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p1077) := by
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
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p123) := by
    exact h16186
  have u6 : p1139 := by
    exact h6761
  rcases h14964 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19566 (p7 p191 p225 p226 p344 p406 p424 p476 p686 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h8348 : p1386)
    (h14965 : p7 ∨ (¬ p191) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p344) ∨ (¬ p406) ∨ (¬ p424) ∨ (¬ p476) ∨ p686 ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p191) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p344) ∨ (¬ p406) ∨ (¬ p424) ∨ (¬ p476) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p191 := by
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
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p406 := by
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
  have u7 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p686) := by
    exact h16205
  have u10 : p1386 := by
    exact h8348
  rcases h14965 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19567 (p7 p129 p163 p544 p657 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h8348 : p1386)
    (h14966 : p7 ∨ p129 ∨ (¬ p163) ∨ (¬ p544) ∨ (¬ p657) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p163) ∨ (¬ p544) ∨ (¬ p657) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p1386 := by
    exact h8348
  rcases h14966 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19568 (p7 p10 p102 p280 p344 p657 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16173 : (¬ p280))
    (h6744 : p1135)
    (h14968 : p7 ∨ (¬ p10) ∨ (¬ p102) ∨ p280 ∨ (¬ p344) ∨ (¬ p657) ∨ (¬ p1135)) : (¬ p10) ∨ (¬ p102) ∨ (¬ p344) ∨ (¬ p657) := by
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
  rcases h14968 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19569 (p7 p261 p279 p304 p426 p537 p726 p836 : Prop)
    (h16152 : (¬ p7))
    (h1444 : p279)
    (h16178 : (¬ p426))
    (h14969 : p7 ∨ (¬ p261) ∨ (¬ p279) ∨ (¬ p304) ∨ p426 ∨ (¬ p537) ∨ (¬ p726) ∨ (¬ p836)) : (¬ p261) ∨ (¬ p304) ∨ (¬ p537) ∨ (¬ p726) ∨ (¬ p836) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p304 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p279 := by
    exact h1444
  have u7 : (¬ p426) := by
    exact h16178
  rcases h14969 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step19570 (p6 p7 p163 p191 p389 p544 p657 p1206 : Prop)
    (h16152 : (¬ p7))
    (h14970 : (¬ p6) ∨ p7 ∨ (¬ p163) ∨ (¬ p191) ∨ (¬ p389) ∨ (¬ p544) ∨ (¬ p657) ∨ (¬ p1206)) : (¬ p6) ∨ (¬ p163) ∨ (¬ p191) ∨ (¬ p389) ∨ (¬ p544) ∨ (¬ p657) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
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
  have u3 : p389 := by
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
  have u6 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h14970 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19571 (p6 p7 p11 p140 p160 p191 p389 p405 p424 p476 p1325 : Prop)
    (h16152 : (¬ p7))
    (h14972 : (¬ p6) ∨ p7 ∨ (¬ p11) ∨ (¬ p140) ∨ (¬ p160) ∨ (¬ p191) ∨ (¬ p389) ∨ (¬ p405) ∨ (¬ p424) ∨ (¬ p476) ∨ (¬ p1325)) : (¬ p6) ∨ (¬ p11) ∨ (¬ p140) ∨ (¬ p160) ∨ (¬ p191) ∨ (¬ p389) ∨ (¬ p405) ∨ (¬ p424) ∨ (¬ p476) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p405 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p476 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h14972 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19572 (p6 p7 p141 p191 p1206 p1443 : Prop)
    (h16152 : (¬ p7))
    (h14973 : (¬ p6) ∨ p7 ∨ (¬ p141) ∨ (¬ p191) ∨ (¬ p1206) ∨ (¬ p1443)) : (¬ p6) ∨ (¬ p141) ∨ (¬ p191) ∨ (¬ p1206) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p191 := by
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
  rcases h14973 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19574 (p7 p344 p666 p686 p710 p1061 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h8348 : p1386)
    (h14975 : p7 ∨ (¬ p344) ∨ (¬ p666) ∨ p686 ∨ (¬ p710) ∨ (¬ p1061) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p344) ∨ (¬ p666) ∨ (¬ p710) ∨ (¬ p1061) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
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
  have u3 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p686) := by
    exact h16205
  have u7 : p1386 := by
    exact h8348
  rcases h14975 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step19576 (p7 p170 p191 p225 p226 p840 : Prop)
    (h16152 : (¬ p7))
    (h14978 : p7 ∨ (¬ p170) ∨ (¬ p191) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p840)) : (¬ p170) ∨ (¬ p191) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p840) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p170 := by
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
  have u4 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14978 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19577 (p7 p344 p638 p836 p1074 p1116 : Prop)
    (h16152 : (¬ p7))
    (h14979 : p7 ∨ (¬ p344) ∨ (¬ p638) ∨ (¬ p836) ∨ (¬ p1074) ∨ (¬ p1116)) : (¬ p344) ∨ (¬ p638) ∨ (¬ p836) ∨ (¬ p1074) ∨ (¬ p1116) := by
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
  have u2 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14979 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19579 (p7 p226 p426 p659 p836 p1036 p1116 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h3753 : p659)
    (h14981 : p7 ∨ (¬ p226) ∨ p426 ∨ (¬ p659) ∨ (¬ p836) ∨ (¬ p1036) ∨ (¬ p1116)) : (¬ p226) ∨ (¬ p836) ∨ (¬ p1036) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1036 := by
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
  have u6 : p659 := by
    exact h3753
  rcases h14981 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step19580 (p7 p101 p124 p190 p211 p323 p382 p521 p789 p815 : Prop)
    (h16152 : (¬ p7))
    (h14982 : p7 ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p190) ∨ (¬ p211) ∨ (¬ p323) ∨ (¬ p382) ∨ (¬ p521) ∨ (¬ p789) ∨ (¬ p815)) : (¬ p101) ∨ (¬ p124) ∨ (¬ p190) ∨ (¬ p211) ∨ (¬ p323) ∨ (¬ p382) ∨ (¬ p521) ∨ (¬ p789) ∨ (¬ p815) := by
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
  have u2 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p521 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p815 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14982 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19581 (p7 p85 p284 p499 p579 p918 : Prop)
    (h16152 : (¬ p7))
    (h14983 : p7 ∨ (¬ p85) ∨ (¬ p284) ∨ (¬ p499) ∨ (¬ p579) ∨ (¬ p918)) : (¬ p85) ∨ (¬ p284) ∨ (¬ p499) ∨ (¬ p579) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p284 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14983 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19582 (p7 p105 p142 p166 p185 p193 : Prop)
    (h16152 : (¬ p7))
    (h14984 : p7 ∨ (¬ p105) ∨ (¬ p142) ∨ (¬ p166) ∨ (¬ p185) ∨ (¬ p193)) : (¬ p105) ∨ (¬ p142) ∨ (¬ p166) ∨ (¬ p185) ∨ (¬ p193) := by
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
  have u2 : p166 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14984 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19583 (p7 p19 p105 p544 p879 p897 : Prop)
    (h16152 : (¬ p7))
    (h14985 : p7 ∨ (¬ p19) ∨ (¬ p105) ∨ (¬ p544) ∨ (¬ p879) ∨ (¬ p897)) : (¬ p19) ∨ (¬ p105) ∨ (¬ p544) ∨ (¬ p879) ∨ (¬ p897) := by
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
  have u2 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p879 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14985 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19584 (p7 p44 p90 p193 p234 p265 p327 p363 p382 p387 p576 : Prop)
    (h16152 : (¬ p7))
    (h14986 : p7 ∨ (¬ p44) ∨ (¬ p90) ∨ (¬ p193) ∨ (¬ p234) ∨ (¬ p265) ∨ (¬ p327) ∨ (¬ p363) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p576)) : (¬ p44) ∨ (¬ p90) ∨ (¬ p193) ∨ (¬ p234) ∨ (¬ p265) ∨ (¬ p327) ∨ (¬ p363) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p576) := by
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
  have u4 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p363 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h14986 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19585 (p7 p90 p237 p265 p304 p576 p664 p904 p923 p1076 : Prop)
    (h16152 : (¬ p7))
    (h14987 : p7 ∨ (¬ p90) ∨ (¬ p237) ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p576) ∨ (¬ p664) ∨ (¬ p904) ∨ (¬ p923) ∨ (¬ p1076)) : (¬ p90) ∨ (¬ p237) ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p576) ∨ (¬ p664) ∨ (¬ p904) ∨ (¬ p923) ∨ (¬ p1076) := by
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
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p923 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14987 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19586 (p7 p90 p125 p237 p265 p303 p576 p665 p1116 : Prop)
    (h16152 : (¬ p7))
    (h14988 : p7 ∨ (¬ p90) ∨ (¬ p125) ∨ (¬ p237) ∨ (¬ p265) ∨ (¬ p303) ∨ (¬ p576) ∨ (¬ p665) ∨ (¬ p1116)) : (¬ p90) ∨ (¬ p125) ∨ (¬ p237) ∨ (¬ p265) ∨ (¬ p303) ∨ (¬ p576) ∨ (¬ p665) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
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
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p576 := by
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
  rcases h14988 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19587 (p7 p105 p140 p167 p189 p256 : Prop)
    (h16152 : (¬ p7))
    (h14989 : p7 ∨ (¬ p105) ∨ (¬ p140) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p256)) : (¬ p105) ∨ (¬ p140) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p140 := by
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
  have u4 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14989 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19588 (p7 p87 p158 p327 p387 p481 p556 p814 p858 p928 : Prop)
    (h16152 : (¬ p7))
    (h14992 : p7 ∨ (¬ p87) ∨ (¬ p158) ∨ (¬ p327) ∨ (¬ p387) ∨ (¬ p481) ∨ (¬ p556) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p928)) : (¬ p87) ∨ (¬ p158) ∨ (¬ p327) ∨ (¬ p387) ∨ (¬ p481) ∨ (¬ p556) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14992 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19589 (p7 p14 p48 p87 p167 p189 : Prop)
    (h16152 : (¬ p7))
    (h14993 : p7 ∨ (¬ p14) ∨ (¬ p48) ∨ (¬ p87) ∨ (¬ p167) ∨ (¬ p189)) : (¬ p14) ∨ (¬ p48) ∨ (¬ p87) ∨ (¬ p167) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14993 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19590 (p7 p8 p47 p87 p158 p189 p229 p664 p928 p1036 : Prop)
    (h16152 : (¬ p7))
    (h14994 : p7 ∨ (¬ p8) ∨ (¬ p47) ∨ (¬ p87) ∨ (¬ p158) ∨ (¬ p189) ∨ (¬ p229) ∨ (¬ p664) ∨ (¬ p928) ∨ (¬ p1036)) : (¬ p8) ∨ (¬ p47) ∨ (¬ p87) ∨ (¬ p158) ∨ (¬ p189) ∨ (¬ p229) ∨ (¬ p664) ∨ (¬ p928) ∨ (¬ p1036) := by
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
  have u3 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14994 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19591 (p7 p17 p87 p158 p303 p420 p579 p665 p928 p1061 : Prop)
    (h16152 : (¬ p7))
    (h14995 : p7 ∨ (¬ p17) ∨ (¬ p87) ∨ (¬ p158) ∨ (¬ p303) ∨ (¬ p420) ∨ (¬ p579) ∨ (¬ p665) ∨ (¬ p928) ∨ (¬ p1061)) : (¬ p17) ∨ (¬ p87) ∨ (¬ p158) ∨ (¬ p303) ∨ (¬ p420) ∨ (¬ p579) ∨ (¬ p665) ∨ (¬ p928) ∨ (¬ p1061) := by
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
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h14995 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19592 (p7 p41 p105 p127 p166 p187 p918 : Prop)
    (h16152 : (¬ p7))
    (h14996 : p7 ∨ (¬ p41) ∨ (¬ p105) ∨ (¬ p127) ∨ (¬ p166) ∨ (¬ p187) ∨ (¬ p918)) : (¬ p41) ∨ (¬ p105) ∨ (¬ p127) ∨ (¬ p166) ∨ (¬ p187) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
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
  have u3 : p166 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h14996 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19593 (p7 p63 p280 p387 p616 p792 p1287 : Prop)
    (h16152 : (¬ p7))
    (h16173 : (¬ p280))
    (h4535 : p792)
    (h14997 : p7 ∨ (¬ p63) ∨ p280 ∨ (¬ p387) ∨ (¬ p616) ∨ (¬ p792) ∨ (¬ p1287)) : (¬ p63) ∨ (¬ p387) ∨ (¬ p616) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p280) := by
    exact h16173
  have u6 : p792 := by
    exact h4535
  rcases h14997 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step19594 (p7 p63 p302 p303 p420 p495 p792 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h4535 : p792)
    (h14998 : p7 ∨ (¬ p63) ∨ p302 ∨ (¬ p303) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p792)) : (¬ p63) ∨ (¬ p303) ∨ (¬ p420) ∨ (¬ p495) := by
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
  have u2 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p302) := by
    exact h16285
  have u6 : p792 := by
    exact h4535
  rcases h14998 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19595 (p7 p10 p105 p126 p141 p167 : Prop)
    (h16152 : (¬ p7))
    (h14999 : p7 ∨ (¬ p10) ∨ (¬ p105) ∨ (¬ p126) ∨ (¬ p141) ∨ (¬ p167)) : (¬ p10) ∨ (¬ p105) ∨ (¬ p126) ∨ (¬ p141) ∨ (¬ p167) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h14999 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19596 (p7 p16 p351 p387 p814 p858 p904 p1096 : Prop)
    (h16152 : (¬ p7))
    (h15001 : p7 ∨ (¬ p16) ∨ (¬ p351) ∨ (¬ p387) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p904) ∨ (¬ p1096)) : (¬ p16) ∨ (¬ p351) ∨ (¬ p387) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p904) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p387 := by
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
  rcases h15001 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19597 (p7 p18 p43 p71 p127 p924 p1099 : Prop)
    (h16152 : (¬ p7))
    (h15002 : p7 ∨ (¬ p18) ∨ (¬ p43) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p924) ∨ (¬ p1099)) : (¬ p18) ∨ (¬ p43) ∨ (¬ p71) ∨ (¬ p127) ∨ (¬ p924) ∨ (¬ p1099) := by
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
  have u4 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15002 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19598 (p7 p9 p16 p17 p301 p302 p303 p343 p904 p1061 p1074 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h1950 : p343)
    (h15003 : p7 ∨ (¬ p9) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p301) ∨ p302 ∨ (¬ p303) ∨ (¬ p343) ∨ (¬ p904) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p9) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p904) ∨ (¬ p1061) ∨ (¬ p1074) := by
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
  have u2 : p17 := by
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
  have u9 : (¬ p302) := by
    exact h16285
  have u10 : p343 := by
    exact h1950
  rcases h15003 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u9 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)

theorem step19599 (p7 p9 p16 p17 p19 p301 p302 p303 p788 p879 p1061 p1074 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h5066 : p788)
    (h15004 : p7 ∨ (¬ p9) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p19) ∨ (¬ p301) ∨ p302 ∨ (¬ p303) ∨ (¬ p788) ∨ (¬ p879) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p9) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p19) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p879) ∨ (¬ p1061) ∨ (¬ p1074) := by
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
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p19 := by
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
  have u6 : p879 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p302) := by
    exact h16285
  have u11 : p788 := by
    exact h5066
  rcases h15004 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u10 q6)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u11)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step19600 (p7 p206 p327 p363 p382 p387 p481 : Prop)
    (h16152 : (¬ p7))
    (h15005 : p7 ∨ (¬ p206) ∨ (¬ p327) ∨ (¬ p363) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p481)) : (¬ p206) ∨ (¬ p327) ∨ (¬ p363) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p481) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p363 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15005 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19601 (p7 p10 p129 p163 p211 p226 p362 p788 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h5066 : p788)
    (h15006 : p7 ∨ (¬ p10) ∨ p129 ∨ (¬ p163) ∨ (¬ p211) ∨ (¬ p226) ∨ (¬ p362) ∨ (¬ p788)) : (¬ p10) ∨ (¬ p163) ∨ (¬ p211) ∨ (¬ p226) ∨ (¬ p362) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p129) := by
    exact h16154
  have u7 : p788 := by
    exact h5066
  rcases h15006 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step19602 (p7 p10 p14 p40 p211 p226 p362 p788 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h5066 : p788)
    (h15007 : p7 ∨ (¬ p10) ∨ (¬ p14) ∨ p40 ∨ (¬ p211) ∨ (¬ p226) ∨ (¬ p362) ∨ (¬ p788)) : (¬ p10) ∨ (¬ p14) ∨ (¬ p211) ∨ (¬ p226) ∨ (¬ p362) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p40) := by
    exact h16150
  have u7 : p788 := by
    exact h5066
  rcases h15007 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step19603 (p7 p19 p44 p90 p193 p265 p304 p323 p350 p576 : Prop)
    (h16152 : (¬ p7))
    (h15008 : p7 ∨ (¬ p19) ∨ (¬ p44) ∨ (¬ p90) ∨ (¬ p193) ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p323) ∨ (¬ p350) ∨ (¬ p576)) : (¬ p19) ∨ (¬ p44) ∨ (¬ p90) ∨ (¬ p193) ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p323) ∨ (¬ p350) ∨ (¬ p576) := by
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
  have u2 : p90 := by
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
  have u5 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15008 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19604 (p7 p127 p129 p163 p226 p323 p427 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h2334 : p427)
    (h15009 : p7 ∨ (¬ p127) ∨ p129 ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p323) ∨ (¬ p427)) : (¬ p127) ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p323) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p127 := by
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
  have u3 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p427 := by
    exact h2334
  rcases h15009 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19605 (p7 p70 p83 p101 p124 p162 p211 p323 p427 p814 p918 p1393 : Prop)
    (h16152 : (¬ p7))
    (h16160 : (¬ p162))
    (h2334 : p427)
    (h15011 : p7 ∨ (¬ p70) ∨ (¬ p83) ∨ (¬ p101) ∨ (¬ p124) ∨ p162 ∨ (¬ p211) ∨ (¬ p323) ∨ (¬ p427) ∨ (¬ p814) ∨ (¬ p918) ∨ (¬ p1393)) : (¬ p70) ∨ (¬ p83) ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p211) ∨ (¬ p323) ∨ (¬ p814) ∨ (¬ p918) ∨ (¬ p1393) := by
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
  have u6 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p162) := by
    exact h16160
  have u11 : p427 := by
    exact h2334
  rcases h15011 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u10 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u11)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step19606 (p7 p70 p85 p980 p1035 p1124 p1140 p1249 : Prop)
    (h16152 : (¬ p7))
    (h15012 : p7 ∨ (¬ p70) ∨ (¬ p85) ∨ (¬ p980) ∨ (¬ p1035) ∨ (¬ p1124) ∨ (¬ p1140) ∨ (¬ p1249)) : (¬ p70) ∨ (¬ p85) ∨ (¬ p980) ∨ (¬ p1035) ∨ (¬ p1124) ∨ (¬ p1140) ∨ (¬ p1249) := by
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
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1124 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15012 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19607 (p7 p187 p211 p227 p790 p802 p1258 p1349 p1452 p1465 : Prop)
    (h16152 : (¬ p7))
    (h15013 : p7 ∨ (¬ p187) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p790) ∨ (¬ p802) ∨ (¬ p1258) ∨ (¬ p1349) ∨ (¬ p1452) ∨ (¬ p1465)) : (¬ p187) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p790) ∨ (¬ p802) ∨ (¬ p1258) ∨ (¬ p1349) ∨ (¬ p1452) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p187 := by
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
  have u3 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p802 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15013 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19608 (p7 p70 p101 p121 p124 p211 p228 p616 p1287 : Prop)
    (h16152 : (¬ p7))
    (h15014 : p7 ∨ (¬ p70) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p124) ∨ (¬ p211) ∨ (¬ p228) ∨ (¬ p616) ∨ (¬ p1287)) : (¬ p70) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p124) ∨ (¬ p211) ∨ (¬ p228) ∨ (¬ p616) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p70 := by
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
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15014 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19609 (p3 p7 p12 p70 p616 p983 p1335 p1545 : Prop)
    (h16152 : (¬ p7))
    (h15015 : (¬ p3) ∨ p7 ∨ (¬ p12) ∨ (¬ p70) ∨ (¬ p616) ∨ (¬ p983) ∨ (¬ p1335) ∨ (¬ p1545)) : (¬ p3) ∨ (¬ p12) ∨ (¬ p70) ∨ (¬ p616) ∨ (¬ p983) ∨ (¬ p1335) ∨ (¬ p1545) := by
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
  have u2 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p983 := by
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
  rcases h15015 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19610 (p7 p39 p68 p88 p101 p121 p124 p211 p228 p814 p858 : Prop)
    (h16152 : (¬ p7))
    (h15016 : p7 ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p124) ∨ (¬ p211) ∨ (¬ p228) ∨ (¬ p814) ∨ (¬ p858)) : (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p124) ∨ (¬ p211) ∨ (¬ p228) ∨ (¬ p814) ∨ (¬ p858) := by
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
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h15016 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19611 (p7 p39 p68 p211 p227 p302 p323 p427 p619 p690 p858 p1022 p1206 p1387 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h2334 : p427)
    (h15017 : p7 ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p211) ∨ (¬ p227) ∨ p302 ∨ (¬ p323) ∨ (¬ p427) ∨ (¬ p619) ∨ (¬ p690) ∨ (¬ p858) ∨ (¬ p1022) ∨ (¬ p1206) ∨ (¬ p1387)) : (¬ p39) ∨ (¬ p68) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p323) ∨ (¬ p619) ∨ (¬ p690) ∨ (¬ p858) ∨ (¬ p1022) ∨ (¬ p1206) ∨ (¬ p1387) := by
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
  have u2 : p211 := by
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
  have u5 : p619 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p690 := by
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
  have u9 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : (¬ p7) := by
    exact h16152
  have u12 : (¬ p302) := by
    exact h16285
  have u13 : p427 := by
    exact h2334
  rcases h15017 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13
  · exact False.elim (u11 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u12 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u13)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u6)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)
  · exact False.elim (q12 u9)
  · exact False.elim (q13 u10)

theorem step19612 (p7 p39 p68 p211 p227 p595 p980 p1232 p1313 p1387 p1452 : Prop)
    (h16152 : (¬ p7))
    (h15018 : p7 ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p595) ∨ (¬ p980) ∨ (¬ p1232) ∨ (¬ p1313) ∨ (¬ p1387) ∨ (¬ p1452)) : (¬ p39) ∨ (¬ p68) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p595) ∨ (¬ p980) ∨ (¬ p1232) ∨ (¬ p1313) ∨ (¬ p1387) ∨ (¬ p1452) := by
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
  have u2 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1313 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h15018 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step19613 (p3 p7 p12 p39 p68 p88 p814 p983 p1015 p1335 : Prop)
    (h16152 : (¬ p7))
    (h15019 : (¬ p3) ∨ p7 ∨ (¬ p12) ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p814) ∨ (¬ p983) ∨ (¬ p1015) ∨ (¬ p1335)) : (¬ p3) ∨ (¬ p12) ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p814) ∨ (¬ p983) ∨ (¬ p1015) ∨ (¬ p1335) := by
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
  have u3 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15019 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19614 (p302 p427 p521 p858 : Prop)
    (h16285 : (¬ p302))
    (h2334 : p427)
    (h15020 : p302 ∨ (¬ p427) ∨ p521 ∨ (¬ p858)) : p521 ∨ (¬ p858) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p521) := fun hu => hn (Or.inl hu)
  have u1 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p302) := by
    exact h16285
  have u3 : p427 := by
    exact h2334
  rcases h15020 with q0 | q1 | q2 | q3
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u1)

theorem step19615 (p7 p101 p143 p287 p309 p1055 p1116 : Prop)
    (h16152 : (¬ p7))
    (h15021 : p7 ∨ (¬ p101) ∨ (¬ p143) ∨ (¬ p287) ∨ (¬ p309) ∨ (¬ p1055) ∨ (¬ p1116)) : (¬ p101) ∨ (¬ p143) ∨ (¬ p287) ∨ (¬ p309) ∨ (¬ p1055) ∨ (¬ p1116) := by
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
  have u4 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15021 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19616 (p3 p7 p39 p63 p68 p544 p664 p1074 p1099 : Prop)
    (h16152 : (¬ p7))
    (h15022 : (¬ p3) ∨ p7 ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p544) ∨ (¬ p664) ∨ (¬ p1074) ∨ (¬ p1099)) : (¬ p3) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p544) ∨ (¬ p664) ∨ (¬ p1074) ∨ (¬ p1099) := by
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
  have u5 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15022 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19617 (p7 p8 p9 p69 p885 p897 : Prop)
    (h16152 : (¬ p7))
    (h15024 : p7 ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p69) ∨ (¬ p885) ∨ (¬ p897)) : (¬ p8) ∨ (¬ p9) ∨ (¬ p69) ∨ (¬ p885) ∨ (¬ p897) := by
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
  have u2 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p885 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15024 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19619 (p7 p70 p85 p102 p127 p1077 p1124 p1249 : Prop)
    (h16152 : (¬ p7))
    (h15026 : p7 ∨ (¬ p70) ∨ (¬ p85) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p1077) ∨ (¬ p1124) ∨ (¬ p1249)) : (¬ p70) ∨ (¬ p85) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p1077) ∨ (¬ p1124) ∨ (¬ p1249) := by
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
  have u2 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15026 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19620 (p7 p40 p69 p303 p427 p595 p996 p1192 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h2334 : p427)
    (h15027 : p7 ∨ p40 ∨ (¬ p69) ∨ (¬ p303) ∨ (¬ p427) ∨ (¬ p595) ∨ (¬ p996) ∨ (¬ p1192)) : (¬ p69) ∨ (¬ p303) ∨ (¬ p595) ∨ (¬ p996) ∨ (¬ p1192) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p40) := by
    exact h16150
  have u7 : p427 := by
    exact h2334
  rcases h15027 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step19621 (p7 p121 p127 p133 p980 p1139 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16157 : (¬ p133))
    (h6761 : p1139)
    (h15028 : p7 ∨ (¬ p121) ∨ (¬ p127) ∨ p133 ∨ (¬ p980) ∨ (¬ p1139) ∨ (¬ p1452)) : (¬ p121) ∨ (¬ p127) ∨ (¬ p980) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p121 := by
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
  have u3 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p133) := by
    exact h16157
  have u6 : p1139 := by
    exact h6761
  rcases h15028 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step19622 (p7 p21 p72 p127 p533 p633 p756 p1141 p1167 p1226 : Prop)
    (h16152 : (¬ p7))
    (h15029 : p7 ∨ (¬ p21) ∨ (¬ p72) ∨ (¬ p127) ∨ (¬ p533) ∨ (¬ p633) ∨ (¬ p756) ∨ (¬ p1141) ∨ (¬ p1167) ∨ (¬ p1226)) : (¬ p21) ∨ (¬ p72) ∨ (¬ p127) ∨ (¬ p533) ∨ (¬ p633) ∨ (¬ p756) ∨ (¬ p1141) ∨ (¬ p1167) ∨ (¬ p1226) := by
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
  have u3 : p533 := by
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
  have u6 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15029 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19623 (p7 p16 p71 p185 p669 p1035 p1115 p1140 p1325 : Prop)
    (h16152 : (¬ p7))
    (h15030 : p7 ∨ (¬ p16) ∨ (¬ p71) ∨ (¬ p185) ∨ (¬ p669) ∨ (¬ p1035) ∨ (¬ p1115) ∨ (¬ p1140) ∨ (¬ p1325)) : (¬ p16) ∨ (¬ p71) ∨ (¬ p185) ∨ (¬ p669) ∨ (¬ p1035) ∨ (¬ p1115) ∨ (¬ p1140) ∨ (¬ p1325) := by
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
  have u3 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1035 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15030 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19624 (p7 p16 p71 p185 p481 p985 p996 p1333 p1584 : Prop)
    (h16152 : (¬ p7))
    (h15031 : p7 ∨ (¬ p16) ∨ (¬ p71) ∨ (¬ p185) ∨ (¬ p481) ∨ (¬ p985) ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p1584)) : (¬ p16) ∨ (¬ p71) ∨ (¬ p185) ∨ (¬ p481) ∨ (¬ p985) ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p1584) := by
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
  have u3 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p985 := by
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
  have u7 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15031 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19625 (p7 p15 p234 p996 p1136 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16259 : (¬ p1136))
    (h8348 : p1386)
    (h15032 : p7 ∨ (¬ p15) ∨ (¬ p234) ∨ (¬ p996) ∨ p1136 ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p15) ∨ (¬ p234) ∨ (¬ p996) ∨ (¬ p1333) := by
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
  have u2 : p996 := by
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
  rcases h15032 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19626 (p7 p15 p16 p185 p234 p669 p996 p1115 : Prop)
    (h16152 : (¬ p7))
    (h15033 : p7 ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p185) ∨ (¬ p234) ∨ (¬ p669) ∨ (¬ p996) ∨ (¬ p1115)) : (¬ p15) ∨ (¬ p16) ∨ (¬ p185) ∨ (¬ p234) ∨ (¬ p669) ∨ (¬ p996) ∨ (¬ p1115) := by
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
  have u3 : p234 := by
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
  have u6 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15033 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19627 (p7 p342 p364 p594 p633 p687 p1545 : Prop)
    (h16152 : (¬ p7))
    (h15034 : p7 ∨ (¬ p342) ∨ (¬ p364) ∨ (¬ p594) ∨ (¬ p633) ∨ (¬ p687) ∨ (¬ p1545)) : (¬ p342) ∨ (¬ p364) ∨ (¬ p594) ∨ (¬ p633) ∨ (¬ p687) ∨ (¬ p1545) := by
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
  have u2 : p594 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15034 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19628 (p4 p7 p8 p10 p102 p312 : Prop)
    (h16152 : (¬ p7))
    (h15035 : (¬ p4) ∨ p7 ∨ (¬ p8) ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p312)) : (¬ p4) ∨ (¬ p8) ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p312) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p312 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15035 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19629 (p7 p10 p102 p185 p224 p263 p302 p362 p836 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h6478 : p1075)
    (h15036 : p7 ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p185) ∨ (¬ p224) ∨ (¬ p263) ∨ p302 ∨ (¬ p362) ∨ (¬ p836) ∨ (¬ p1075)) : (¬ p10) ∨ (¬ p102) ∨ (¬ p185) ∨ (¬ p224) ∨ (¬ p263) ∨ (¬ p362) ∨ (¬ p836) := by
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
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p263 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p302) := by
    exact h16285
  have u9 : p1075 := by
    exact h6478
  rcases h15036 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19630 (p7 p41 p87 p102 p127 p185 p187 p224 p302 p897 p926 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h6478 : p1075)
    (h15037 : p7 ∨ (¬ p41) ∨ (¬ p87) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p224) ∨ p302 ∨ (¬ p897) ∨ (¬ p926) ∨ (¬ p1075)) : (¬ p41) ∨ (¬ p87) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p185) ∨ (¬ p187) ∨ (¬ p224) ∨ (¬ p897) ∨ (¬ p926) := by
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
  have u2 : p102 := by
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
  have u5 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p302) := by
    exact h16285
  have u11 : p1075 := by
    exact h6478
  rcases h15037 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
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

theorem step19631 (p7 p11 p17 p87 p455 p580 : Prop)
    (h16152 : (¬ p7))
    (h15038 : p7 ∨ (¬ p11) ∨ (¬ p17) ∨ (¬ p87) ∨ (¬ p455) ∨ (¬ p580)) : (¬ p11) ∨ (¬ p17) ∨ (¬ p87) ∨ (¬ p455) ∨ (¬ p580) := by
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
  have u2 : p87 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15038 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19632 (p7 p301 p366 p382 p383 p1443 : Prop)
    (h16152 : (¬ p7))
    (h15039 : p7 ∨ (¬ p301) ∨ (¬ p366) ∨ (¬ p382) ∨ (¬ p383) ∨ (¬ p1443)) : (¬ p301) ∨ (¬ p366) ∨ (¬ p382) ∨ (¬ p383) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p383 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15039 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19633 (p7 p124 p262 p342 p515 p581 p1385 : Prop)
    (h16152 : (¬ p7))
    (h15040 : p7 ∨ (¬ p124) ∨ (¬ p262) ∨ (¬ p342) ∨ (¬ p515) ∨ (¬ p581) ∨ (¬ p1385)) : (¬ p124) ∨ (¬ p262) ∨ (¬ p342) ∨ (¬ p515) ∨ (¬ p581) ∨ (¬ p1385) := by
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
  have u2 : p342 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p515 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h15040 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step19634 (p7 p41 p83 p102 p189 p255 p257 p918 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h7053 : p1184)
    (h15041 : p7 ∨ (¬ p41) ∨ (¬ p83) ∨ (¬ p102) ∨ (¬ p189) ∨ (¬ p255) ∨ p257 ∨ (¬ p918) ∨ (¬ p1184)) : (¬ p41) ∨ (¬ p83) ∨ (¬ p102) ∨ (¬ p189) ∨ (¬ p255) ∨ (¬ p918) := by
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
  have u2 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p257) := by
    exact h16170
  have u8 : p1184 := by
    exact h7053
  rcases h15041 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u8)

theorem step19636 (p4 p7 p290 p420 p633 p840 : Prop)
    (h16152 : (¬ p7))
    (h15043 : (¬ p4) ∨ p7 ∨ (¬ p290) ∨ (¬ p420) ∨ (¬ p633) ∨ (¬ p840)) : (¬ p4) ∨ (¬ p290) ∨ (¬ p420) ∨ (¬ p633) ∨ (¬ p840) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p290 := by
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
  have u4 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15043 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19637 (p7 p16 p17 p71 p224 p301 p348 p481 p1189 p1334 p1542 : Prop)
    (h16152 : (¬ p7))
    (h15045 : p7 ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p71) ∨ (¬ p224) ∨ (¬ p301) ∨ p348 ∨ (¬ p481) ∨ (¬ p1189) ∨ (¬ p1334) ∨ (¬ p1542)) : (¬ p16) ∨ (¬ p17) ∨ (¬ p71) ∨ (¬ p224) ∨ (¬ p301) ∨ p348 ∨ (¬ p481) ∨ (¬ p1189) ∨ (¬ p1334) ∨ (¬ p1542) := by
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
  have u2 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p348) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h15045 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u10 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u5 q6)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)
  · exact False.elim (q10 u9)

theorem step19638 (p7 p16 p71 p185 p303 p348 p481 p836 p1334 p1366 : Prop)
    (h16152 : (¬ p7))
    (h15046 : p7 ∨ (¬ p16) ∨ (¬ p71) ∨ (¬ p185) ∨ (¬ p303) ∨ (¬ p348) ∨ (¬ p481) ∨ (¬ p836) ∨ (¬ p1334) ∨ (¬ p1366)) : (¬ p16) ∨ (¬ p71) ∨ (¬ p185) ∨ (¬ p303) ∨ (¬ p348) ∨ (¬ p481) ∨ (¬ p836) ∨ (¬ p1334) ∨ (¬ p1366) := by
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
  have u4 : p348 := by
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
  have u7 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h15046 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19639 (p7 p70 p121 p127 p161 p983 p1081 p1232 : Prop)
    (h16152 : (¬ p7))
    (h15047 : p7 ∨ (¬ p70) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p161) ∨ (¬ p983) ∨ (¬ p1081) ∨ (¬ p1232)) : (¬ p70) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p161) ∨ (¬ p983) ∨ (¬ p1081) ∨ (¬ p1232) := by
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
  have u4 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15047 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19640 (p7 p17 p45 p129 p190 p481 p581 p996 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h8348 : p1386)
    (h15048 : p7 ∨ (¬ p17) ∨ (¬ p45) ∨ p129 ∨ (¬ p190) ∨ (¬ p481) ∨ (¬ p581) ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p17) ∨ (¬ p45) ∨ (¬ p190) ∨ (¬ p481) ∨ (¬ p581) ∨ (¬ p996) ∨ (¬ p1333) := by
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
  have u2 : p190 := by
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
  have u8 : (¬ p129) := by
    exact h16154
  have u9 : p1386 := by
    exact h8348
  rcases h15048 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19641 (p7 p70 p85 p280 p301 p481 p576 p996 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16173 : (¬ p280))
    (h8348 : p1386)
    (h15049 : p7 ∨ (¬ p70) ∨ (¬ p85) ∨ p280 ∨ (¬ p301) ∨ (¬ p481) ∨ (¬ p576) ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p70) ∨ (¬ p85) ∨ (¬ p301) ∨ (¬ p481) ∨ (¬ p576) ∨ (¬ p996) ∨ (¬ p1333) := by
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
  have u2 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
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
  have u8 : (¬ p280) := by
    exact h16173
  have u9 : p1386 := by
    exact h8348
  rcases h15049 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step19642 (p7 p70 p669 p1035 p1074 p1099 p1140 p1325 : Prop)
    (h16152 : (¬ p7))
    (h15050 : p7 ∨ (¬ p70) ∨ (¬ p669) ∨ (¬ p1035) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1140) ∨ (¬ p1325)) : (¬ p70) ∨ (¬ p669) ∨ (¬ p1035) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1140) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1035 := by
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
  have u5 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h15050 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19643 (p7 p17 p87 p301 p406 p431 p438 p816 p1393 : Prop)
    (h16152 : (¬ p7))
    (h15051 : p7 ∨ (¬ p17) ∨ (¬ p87) ∨ (¬ p301) ∨ (¬ p406) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p816) ∨ (¬ p1393)) : (¬ p17) ∨ (¬ p87) ∨ (¬ p301) ∨ (¬ p406) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p816) ∨ (¬ p1393) := by
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
  have u2 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p406 := by
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
  have u6 : p816 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h15051 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step19644 (p7 p102 p342 p420 p455 p1206 : Prop)
    (h16152 : (¬ p7))
    (h15052 : p7 ∨ (¬ p102) ∨ (¬ p342) ∨ (¬ p420) ∨ (¬ p455) ∨ (¬ p1206)) : (¬ p102) ∨ (¬ p342) ∨ (¬ p420) ∨ (¬ p455) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
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
  have u3 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15052 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19646 (p7 p70 p456 p481 p495 p532 p1330 p1366 : Prop)
    (h16152 : (¬ p7))
    (h15055 : p7 ∨ (¬ p70) ∨ (¬ p456) ∨ (¬ p481) ∨ (¬ p495) ∨ (¬ p532) ∨ (¬ p1330) ∨ (¬ p1366)) : (¬ p70) ∨ (¬ p456) ∨ (¬ p481) ∨ (¬ p495) ∨ (¬ p532) ∨ (¬ p1330) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p456 := by
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
  have u4 : p532 := by
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
  rcases h15055 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19647 (p7 p435 p617 p687 p980 p996 p1074 p1099 p1135 p1324 : Prop)
    (h16152 : (¬ p7))
    (h6744 : p1135)
    (h16309 : (¬ p1324))
    (h15056 : p7 ∨ (¬ p435) ∨ (¬ p617) ∨ (¬ p687) ∨ (¬ p980) ∨ (¬ p996) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1135) ∨ p1324) : (¬ p435) ∨ (¬ p617) ∨ (¬ p687) ∨ (¬ p980) ∨ (¬ p996) ∨ (¬ p1074) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p1135 := by
    exact h6744
  have u9 : (¬ p1324) := by
    exact h16309
  rcases h15056 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u8)
  · exact False.elim (u9 q9)

theorem step19648 (p7 p70 p481 p980 p1074 p1099 p1330 p1366 : Prop)
    (h16152 : (¬ p7))
    (h15057 : p7 ∨ (¬ p70) ∨ (¬ p481) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1330) ∨ (¬ p1366)) : (¬ p70) ∨ (¬ p481) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1330) ∨ (¬ p1366) := by
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
  rcases h15057 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step19649 (p4 p7 p10 p102 p290 p840 : Prop)
    (h16152 : (¬ p7))
    (h15058 : (¬ p4) ∨ p7 ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p290) ∨ (¬ p840)) : (¬ p4) ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p290) ∨ (¬ p840) := by
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
  have u2 : p102 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h15058 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step19650 (p7 p10 p102 p362 p496 p980 p1074 p1075 p1099 p1324 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16309 : (¬ p1324))
    (h15059 : p7 ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p362) ∨ (¬ p496) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1075) ∨ (¬ p1099) ∨ p1324) : (¬ p10) ∨ (¬ p102) ∨ (¬ p362) ∨ (¬ p496) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1099) := by
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
  have u3 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : p1075 := by
    exact h6478
  have u9 : (¬ p1324) := by
    exact h16309
  rcases h15059 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u6)
  · exact False.elim (u9 q9)

theorem step19651 (p7 p40 p69 p387 p499 p601 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h6744 : p1135)
    (h15060 : p7 ∨ p40 ∨ (¬ p69) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1135)) : (¬ p69) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) := by
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
  have u5 : (¬ p40) := by
    exact h16150
  have u6 : p1135 := by
    exact h6744
  rcases h15060 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step19653 (p7 p84 p193 p424 p929 p980 p1055 p1102 p1330 p1366 : Prop)
    (h16152 : (¬ p7))
    (h15066 : p7 ∨ (¬ p84) ∨ (¬ p193) ∨ (¬ p424) ∨ (¬ p929) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1102) ∨ (¬ p1330) ∨ (¬ p1366)) : (¬ p84) ∨ (¬ p193) ∨ (¬ p424) ∨ (¬ p929) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1102) ∨ (¬ p1330) ∨ (¬ p1366) := by
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
  have u3 : p929 := by
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
  have u6 : p1102 := by
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
  rcases h15066 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

#print axioms step19653

end NineRUPTrial
