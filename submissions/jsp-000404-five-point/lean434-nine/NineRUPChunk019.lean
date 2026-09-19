import Mathlib.Tactic.Tauto

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineRUPTrial

theorem step27878 (p108 p134 p163 p167 : Prop)
    (h26843 : p167 ∨ p163)
    (h12269 : (¬ p108) ∨ p134 ∨ (¬ p167)) : (¬ p108) ∨ p163 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h12269 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)

theorem step27879 (p3 p105 p121 p211 p226 p227 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26847 : p226 ∨ p3)
    (h17308 : (¬ p105) ∨ (¬ p211) ∨ (¬ p226) ∨ (¬ p227) ∨ (¬ p1206)) : p121 ∨ (¬ p227) ∨ (¬ p211) ∨ p3 ∨ (¬ p105) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17308 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)

theorem step27880 (p105 p134 p142 p166 p185 p189 p193 : Prop)
    (h26841 : p142 ∨ p134)
    (h26845 : p193 ∨ p189)
    (h19582 : (¬ p105) ∨ (¬ p142) ∨ (¬ p166) ∨ (¬ p185) ∨ (¬ p193)) : (¬ p185) ∨ (¬ p166) ∨ (¬ p105) ∨ p134 ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p166 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19582 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u6)

theorem step27881 (p14 p25 p105 p125 p210 p229 p420 p601 : Prop)
    (h26881 : p601 ∨ p420)
    (h26849 : p229 ∨ p14)
    (h18765 : (¬ p25) ∨ (¬ p105) ∨ (¬ p125) ∨ (¬ p210) ∨ (¬ p229) ∨ (¬ p601)) : (¬ p210) ∨ (¬ p25) ∨ (¬ p105) ∨ (¬ p125) ∨ p420 ∨ p14 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p25 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u7 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18765 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u6)

theorem step27882 (p3 p10 p105 p125 p211 p226 p362 : Prop)
    (h26865 : p362 ∨ p125)
    (h26847 : p226 ∨ p3)
    (h18628 : (¬ p10) ∨ (¬ p105) ∨ (¬ p211) ∨ (¬ p226) ∨ (¬ p362)) : (¬ p10) ∨ p125 ∨ p3 ∨ (¬ p105) ∨ (¬ p211) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p125) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18628 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step27883 (p10 p105 p126 p141 p163 p167 : Prop)
    (h26843 : p167 ∨ p163)
    (h19595 : (¬ p10) ∨ (¬ p105) ∨ (¬ p126) ∨ (¬ p141) ∨ (¬ p167)) : (¬ p10) ∨ p163 ∨ (¬ p141) ∨ (¬ p126) ∨ (¬ p105) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19595 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step27884 (p3 p105 p226 p324 p382 p406 p419 p475 : Prop)
    (h26869 : p406 ∨ p382)
    (h26847 : p226 ∨ p3)
    (h16223 : (¬ p105) ∨ (¬ p226) ∨ (¬ p324) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p475)) : p382 ∨ p3 ∨ (¬ p475) ∨ (¬ p419) ∨ (¬ p324) ∨ (¬ p105) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p475 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p324 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16223 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)

theorem step27885 (p17 p105 p140 p163 p167 p189 p256 : Prop)
    (h26853 : p256 ∨ p17)
    (h26843 : p167 ∨ p163)
    (h19587 : (¬ p105) ∨ (¬ p140) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p256)) : p17 ∨ (¬ p105) ∨ (¬ p140) ∨ (¬ p189) ∨ p163 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p17) := fun hu => hn (Or.inl hu)
  have u1 : p105 := by
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
  have u4 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19587 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step27886 (p41 p45 p105 p140 p163 p167 p576 p581 : Prop)
    (h26831 : p45 ∨ p41)
    (h26879 : p581 ∨ p576)
    (h26843 : p167 ∨ p163)
    (h17357 : (¬ p45) ∨ (¬ p105) ∨ (¬ p140) ∨ (¬ p167) ∨ (¬ p581)) : p41 ∨ p576 ∨ (¬ p140) ∨ (¬ p105) ∨ p163 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p41) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17357 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)

theorem step27896 (p8 p163 p424 p540 p563 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h16972 : (¬ p8) ∨ (¬ p163) ∨ (¬ p540) ∨ (¬ p563) ∨ (¬ p796)) : p424 ∨ (¬ p163) ∨ (¬ p540) ∨ (¬ p563) ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p163 := by
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
  have u4 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16972 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step27897 (p2 p185 p194 p237 p540 p836 p840 : Prop)
    (h26851 : p237 ∨ p185)
    (h26895 : p840 ∨ p836)
    (h17168 : (¬ p2) ∨ (¬ p194) ∨ (¬ p237) ∨ (¬ p540) ∨ (¬ p840)) : (¬ p2) ∨ p185 ∨ p836 ∨ (¬ p194) ∨ (¬ p540) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17168 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)

theorem step27898 (p14 p234 p534 p540 p738 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h17994 : (¬ p14) ∨ (¬ p534) ∨ (¬ p540) ∨ (¬ p738) ∨ (¬ p1187)) : (¬ p534) ∨ p234 ∨ (¬ p540) ∨ (¬ p14) ∨ (¬ p738) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p234) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p738 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17994 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step27900 (p6 p134 p142 p344 p424 p540 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26841 : p142 ∨ p134)
    (h19538 : (¬ p6) ∨ (¬ p142) ∨ (¬ p344) ∨ (¬ p540) ∨ (¬ p796)) : p424 ∨ (¬ p344) ∨ p134 ∨ (¬ p540) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19538 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step27901 (p8 p14 p234 p540 p563 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h17865 : (¬ p8) ∨ (¬ p14) ∨ (¬ p540) ∨ (¬ p563) ∨ (¬ p1187)) : p234 ∨ (¬ p8) ∨ (¬ p563) ∨ (¬ p540) ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p563 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17865 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step27902 (p2 p3 p172 p540 p836 p840 : Prop)
    (h26895 : p840 ∨ p836)
    (h19376 : (¬ p2) ∨ (¬ p3) ∨ (¬ p172) ∨ (¬ p540) ∨ (¬ p840)) : (¬ p3) ∨ (¬ p2) ∨ (¬ p540) ∨ p836 ∨ (¬ p172) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19376 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step27903 (p12 p163 p424 p540 p668 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h19539 : (¬ p12) ∨ (¬ p163) ∨ (¬ p540) ∨ (¬ p668) ∨ (¬ p796)) : p424 ∨ (¬ p540) ∨ (¬ p12) ∨ (¬ p163) ∨ (¬ p668) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19539 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step27904 (p8 p15 p69 p419 p540 p563 p940 p996 p1325 p1333 p1570 p1674 : Prop)
    (h26833 : p69 ∨ p15)
    (h26905 : p996 ∨ p419)
    (h26931 : p1333 ∨ p1325)
    (h20478 : (¬ p8) ∨ (¬ p69) ∨ (¬ p540) ∨ (¬ p563) ∨ (¬ p940) ∨ (¬ p996) ∨ (¬ p1333) ∨ (¬ p1570) ∨ (¬ p1674)) : (¬ p1570) ∨ (¬ p1674) ∨ p15 ∨ (¬ p563) ∨ (¬ p8) ∨ p419 ∨ (¬ p540) ∨ p1325 ∨ (¬ p940) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1570 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1674 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p563 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p540 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20478 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u1)

theorem step27905 (p14 p67 p229 : Prop)
    (h26849 : p229 ∨ p14)
    (h16452 : p67 ∨ (¬ p229)) : p67 ∨ p14 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p67) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p14) := fun hu => hn (Or.inr hu)
  have u2 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16452 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)

theorem step27906 (p14 p229 p234 p539 : Prop)
    (h26849 : p229 ∨ p14)
    (h12807 : (¬ p229) ∨ (¬ p234) ∨ (¬ p539)) : p14 ∨ (¬ p539) ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p539 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h12807 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)

theorem step27908 (p14 p229 p234 p382 p406 p476 p1325 p1333 : Prop)
    (h26869 : p406 ∨ p382)
    (h26849 : p229 ∨ p14)
    (h26931 : p1333 ∨ p1325)
    (h18002 : (¬ p229) ∨ (¬ p234) ∨ (¬ p406) ∨ (¬ p476) ∨ (¬ p1333)) : p382 ∨ (¬ p476) ∨ p14 ∨ p1325 ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p476 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18002 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)

theorem step27909 (p3 p14 p121 p229 p423 p532 p1000 p1206 p1325 p1333 : Prop)
    (h26849 : p229 ∨ p14)
    (h26931 : p1333 ∨ p1325)
    (h26923 : p1206 ∨ p121)
    (h18630 : (¬ p3) ∨ (¬ p229) ∨ (¬ p423) ∨ (¬ p532) ∨ (¬ p1000) ∨ (¬ p1206) ∨ (¬ p1333)) : p14 ∨ (¬ p3) ∨ (¬ p532) ∨ p1325 ∨ (¬ p423) ∨ p121 ∨ (¬ p1000) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18630 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u8)

theorem step27910 (p12 p14 p229 p234 p543 p664 p1036 : Prop)
    (h26849 : p229 ∨ p14)
    (h26907 : p1036 ∨ p12)
    (h19171 : (¬ p229) ∨ (¬ p234) ∨ (¬ p543) ∨ (¬ p664) ∨ (¬ p1036)) : p14 ∨ p12 ∨ (¬ p234) ∨ (¬ p664) ∨ (¬ p543) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p543 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19171 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)

theorem step27911 (p3 p14 p229 p303 p387 p420 p495 p499 p601 p1004 p1140 p1159 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26881 : p601 ∨ p420)
    (h26875 : p499 ∨ p495)
    (h26867 : p387 ∨ p303)
    (h26849 : p229 ∨ p14)
    (h19402 : (¬ p3) ∨ (¬ p229) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1004) ∨ (¬ p1159)) : p1140 ∨ (¬ p1004) ∨ (¬ p3) ∨ p420 ∨ p495 ∨ p303 ∨ p14 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19402 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step27912 (p2 p14 p229 p234 p1140 : Prop)
    (h26849 : p229 ∨ p14)
    (h20166 : (¬ p2) ∨ (¬ p229) ∨ (¬ p234) ∨ (¬ p1140)) : (¬ p2) ∨ (¬ p1140) ∨ p14 ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20166 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)

theorem step27913 (p3 p14 p68 p229 : Prop)
    (h26849 : p229 ∨ p14)
    (h5074 : (¬ p3) ∨ (¬ p68) ∨ (¬ p229)) : (¬ p68) ∨ p14 ∨ (¬ p3) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p14) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h5074 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)

theorem step27914 (p14 p43 p163 p229 p1385 p1393 : Prop)
    (h26849 : p229 ∨ p14)
    (h26933 : p1393 ∨ p1385)
    (h25805 : (¬ p1393) ∨ (¬ p43) ∨ (¬ p229) ∨ (¬ p163)) : p14 ∨ p1385 ∨ (¬ p163) ∨ (¬ p43) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25805 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step27915 (p3 p14 p229 p422 p1140 p1159 p1256 : Prop)
    (h26929 : p1256 ∨ p422)
    (h26919 : p1159 ∨ p1140)
    (h26849 : p229 ∨ p14)
    (h25806 : (¬ p1159) ∨ (¬ p229) ∨ (¬ p1256) ∨ (¬ p3)) : (¬ p3) ∨ p422 ∨ p1140 ∨ p14 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25806 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step27916 (p2 p3 p14 p17 p229 p256 p576 p800 p1385 p1393 : Prop)
    (h26853 : p256 ∨ p17)
    (h26849 : p229 ∨ p14)
    (h26933 : p1393 ∨ p1385)
    (h17972 : (¬ p2) ∨ (¬ p3) ∨ (¬ p229) ∨ (¬ p256) ∨ (¬ p576) ∨ (¬ p800) ∨ (¬ p1393)) : (¬ p800) ∨ p17 ∨ (¬ p3) ∨ p14 ∨ (¬ p2) ∨ p1385 ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p800 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17972 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u9)

theorem step27917 (p2 p3 p14 p229 p419 : Prop)
    (h26849 : p229 ∨ p14)
    (h18531 : (¬ p2) ∨ (¬ p3) ∨ (¬ p229) ∨ (¬ p419)) : p14 ∨ (¬ p3) ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18531 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step27918 (p2 p3 p14 p229 p382 p406 p690 p1191 p1287 : Prop)
    (h26849 : p229 ∨ p14)
    (h26869 : p406 ∨ p382)
    (h19919 : (¬ p2) ∨ (¬ p3) ∨ (¬ p229) ∨ (¬ p406) ∨ (¬ p690) ∨ (¬ p1191) ∨ (¬ p1287)) : (¬ p3) ∨ (¬ p1191) ∨ p14 ∨ (¬ p2) ∨ (¬ p1287) ∨ (¬ p690) ∨ p382 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19919 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u4)

theorem step27919 (p2 p3 p14 p18 p19 p229 p326 : Prop)
    (h26849 : p229 ∨ p14)
    (h26829 : p19 ∨ p18)
    (h20387 : (¬ p2) ∨ (¬ p3) ∨ (¬ p19) ∨ (¬ p229) ∨ (¬ p326)) : p14 ∨ (¬ p3) ∨ (¬ p326) ∨ (¬ p2) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20387 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)

theorem step27920 (p3 p14 p17 p71 p229 p234 p256 p576 p790 p803 p814 : Prop)
    (h26853 : p256 ∨ p17)
    (h26849 : p229 ∨ p14)
    (h26893 : p814 ∨ p790)
    (h17720 : (¬ p3) ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p234) ∨ (¬ p256) ∨ (¬ p576) ∨ (¬ p803) ∨ (¬ p814)) : p17 ∨ (¬ p576) ∨ p14 ∨ (¬ p71) ∨ (¬ p803) ∨ p790 ∨ (¬ p3) ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p17) := fun hu => hn (Or.inl hu)
  have u1 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p803 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17720 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u10)

theorem step27924 (p3 p14 p71 p125 p229 p362 p420 p423 p961 p1210 : Prop)
    (h26865 : p362 ∨ p125)
    (h26849 : p229 ∨ p14)
    (h19202 : (¬ p3) ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p423) ∨ (¬ p961) ∨ (¬ p1210)) : (¬ p1210) ∨ (¬ p420) ∨ (¬ p3) ∨ (¬ p423) ∨ p125 ∨ (¬ p961) ∨ p14 ∨ (¬ p71) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1210 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19202 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u0)

theorem step27925 (p3 p14 p71 p229 p234 p419 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26849 : p229 ∨ p14)
    (h20524 : (¬ p3) ∨ (¬ p71) ∨ (¬ p229) ∨ (¬ p234) ∨ (¬ p996)) : (¬ p71) ∨ p419 ∨ (¬ p234) ∨ (¬ p3) ∨ p14 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20524 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step27926 (p14 p47 p163 p229 : Prop)
    (h26849 : p229 ∨ p14)
    (h12169 : (¬ p47) ∨ (¬ p163) ∨ (¬ p229)) : p14 ∨ (¬ p47) ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h12169 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step27928 (p3 p14 p125 p229 p265 p303 p423 p576 p1000 : Prop)
    (h26849 : p229 ∨ p14)
    (h19124 : (¬ p3) ∨ (¬ p125) ∨ (¬ p229) ∨ (¬ p265) ∨ (¬ p303) ∨ (¬ p423) ∨ (¬ p576) ∨ (¬ p1000)) : p14 ∨ (¬ p265) ∨ (¬ p1000) ∨ (¬ p576) ∨ (¬ p303) ∨ (¬ p3) ∨ (¬ p125) ∨ (¬ p423) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19124 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u2)

theorem step27929 (p14 p15 p17 p69 p225 p229 p576 p581 p790 p838 : Prop)
    (h26849 : p229 ∨ p14)
    (h26879 : p581 ∨ p576)
    (h26833 : p69 ∨ p15)
    (h18966 : (¬ p17) ∨ (¬ p69) ∨ (¬ p225) ∨ (¬ p229) ∨ (¬ p581) ∨ (¬ p790) ∨ (¬ p838)) : p14 ∨ (¬ p838) ∨ (¬ p790) ∨ p576 ∨ (¬ p225) ∨ (¬ p17) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p838 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18966 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u1)

theorem step27932 (p3 p14 p43 p135 p187 p229 p576 p581 : Prop)
    (h26849 : p229 ∨ p14)
    (h26879 : p581 ∨ p576)
    (h17719 : (¬ p3) ∨ (¬ p43) ∨ (¬ p135) ∨ (¬ p187) ∨ (¬ p229) ∨ (¬ p581)) : (¬ p3) ∨ p14 ∨ p576 ∨ (¬ p187) ∨ (¬ p43) ∨ (¬ p135) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p14) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17719 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)

theorem step27933 (p14 p43 p90 p163 p189 p193 p229 : Prop)
    (h26849 : p229 ∨ p14)
    (h26586 : p90)
    (h26845 : p193 ∨ p189)
    (h18532 : (¬ p43) ∨ (¬ p90) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p229)) : p14 ∨ (¬ p43) ∨ (¬ p163) ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p90 := by
    exact h26586
  have u6 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18532 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)

theorem step27934 (p14 p43 p135 p163 p229 p576 p581 : Prop)
    (h26849 : p229 ∨ p14)
    (h26879 : p581 ∨ p576)
    (h19108 : (¬ p43) ∨ (¬ p135) ∨ (¬ p163) ∨ (¬ p229) ∨ (¬ p581)) : p14 ∨ (¬ p43) ∨ (¬ p135) ∨ (¬ p163) ∨ p576 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19108 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step27935 (p14 p169 p185 p189 p229 p237 : Prop)
    (h26849 : p229 ∨ p14)
    (h26851 : p237 ∨ p185)
    (h25808 : (¬ p237) ∨ (¬ p169) ∨ (¬ p189) ∨ (¬ p229)) : p14 ∨ p185 ∨ (¬ p169) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p169 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25808 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step27938 (p3 p6 p14 p229 p423 : Prop)
    (h26849 : p229 ∨ p14)
    (h19382 : (¬ p3) ∨ (¬ p6) ∨ (¬ p229) ∨ (¬ p423)) : p14 ∨ (¬ p423) ∨ (¬ p6) ∨ (¬ p3) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19382 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)

theorem step27939 (p14 p18 p19 p104 p124 p213 p229 : Prop)
    (h26849 : p229 ∨ p14)
    (h26829 : p19 ∨ p18)
    (h18562 : (¬ p19) ∨ (¬ p104) ∨ (¬ p124) ∨ (¬ p213) ∨ (¬ p229)) : p14 ∨ (¬ p104) ∨ (¬ p213) ∨ (¬ p124) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18562 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step27942 (p14 p18 p108 p229 : Prop)
    (h26849 : p229 ∨ p14)
    (h11998 : p18 ∨ (¬ p108) ∨ (¬ p229)) : p14 ∨ (¬ p108) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h11998 with q0 | q1 | q2
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step27944 (p12 p14 p72 p229 p561 p1036 p1055 p1061 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26907 : p1036 ∨ p12)
    (h26849 : p229 ∨ p14)
    (h17212 : (¬ p72) ∨ (¬ p229) ∨ (¬ p561) ∨ (¬ p1036) ∨ (¬ p1061)) : p1055 ∨ p12 ∨ (¬ p561) ∨ p14 ∨ (¬ p72) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1055) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17212 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step27947 (p12 p14 p18 p19 p229 p1036 p1076 p1077 : Prop)
    (h26849 : p229 ∨ p14)
    (h26907 : p1036 ∨ p12)
    (h26911 : p1077 ∨ p1076)
    (h26829 : p19 ∨ p18)
    (h20394 : (¬ p19) ∨ (¬ p229) ∨ (¬ p1036) ∨ (¬ p1077)) : p14 ∨ p12 ∨ p1076 ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20394 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)

theorem step27949 (p14 p18 p19 p229 p560 p980 p1055 : Prop)
    (h26849 : p229 ∨ p14)
    (h26829 : p19 ∨ p18)
    (h18604 : (¬ p19) ∨ (¬ p229) ∨ (¬ p560) ∨ (¬ p980) ∨ (¬ p1055)) : p14 ∨ (¬ p560) ∨ (¬ p1055) ∨ (¬ p980) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18604 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)

theorem step27950 (p8 p14 p18 p19 p224 p229 p560 p710 : Prop)
    (h26849 : p229 ∨ p14)
    (h26889 : p710 ∨ p8)
    (h26829 : p19 ∨ p18)
    (h20099 : (¬ p19) ∨ (¬ p224) ∨ (¬ p229) ∨ (¬ p560) ∨ (¬ p710)) : (¬ p560) ∨ p14 ∨ p8 ∨ p18 ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p14) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20099 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u6)

theorem step27951 (p8 p14 p18 p19 p229 p344 p560 p710 : Prop)
    (h26829 : p19 ∨ p18)
    (h26889 : p710 ∨ p8)
    (h26849 : p229 ∨ p14)
    (h20056 : (¬ p19) ∨ (¬ p229) ∨ (¬ p344) ∨ (¬ p560) ∨ (¬ p710)) : (¬ p560) ∨ p18 ∨ p8 ∨ p14 ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20056 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u6)

theorem step27952 (p14 p229 p420 p434 p495 p499 p560 p601 p980 p1055 p1330 : Prop)
    (h26875 : p499 ∨ p495)
    (h26849 : p229 ∨ p14)
    (h26881 : p601 ∨ p420)
    (h19406 : (¬ p229) ∨ (¬ p434) ∨ (¬ p499) ∨ (¬ p560) ∨ (¬ p601) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1330)) : (¬ p434) ∨ p495 ∨ (¬ p1055) ∨ (¬ p560) ∨ (¬ p980) ∨ (¬ p1330) ∨ p14 ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19406 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u5)

theorem step27953 (p14 p15 p24 p69 p105 p229 p495 p499 : Prop)
    (h26849 : p229 ∨ p14)
    (h26875 : p499 ∨ p495)
    (h26833 : p69 ∨ p15)
    (h18682 : (¬ p24) ∨ (¬ p69) ∨ (¬ p105) ∨ (¬ p229) ∨ (¬ p499)) : p14 ∨ (¬ p24) ∨ (¬ p105) ∨ p495 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18682 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step27954 (p101 p102 p121 p161 p964 p980 p983 p1206 p1231 : Prop)
    (h26903 : p983 ∨ p980)
    (h26837 : p102 ∨ p101)
    (h26923 : p1206 ∨ p121)
    (h18808 : (¬ p102) ∨ (¬ p161) ∨ (¬ p964) ∨ (¬ p983) ∨ (¬ p1206) ∨ (¬ p1231)) : p980 ∨ (¬ p161) ∨ p101 ∨ p121 ∨ (¬ p964) ∨ (¬ p1231) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p964 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1231 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18808 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u5)

theorem step27955 (p17 p86 p161 p256 p258 p288 p533 p756 p1229 p1232 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h26855 : p288 ∨ p258)
    (h26853 : p256 ∨ p17)
    (h16957 : (¬ p86) ∨ (¬ p161) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p533) ∨ (¬ p756) ∨ (¬ p1232)) : (¬ p756) ∨ p1229 ∨ (¬ p533) ∨ p258 ∨ p17 ∨ (¬ p161) ∨ (¬ p86) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16957 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u7)

theorem step27959 (p6 p10 p68 p127 p161 p303 p323 p387 p864 p1147 p1508 : Prop)
    (h26861 : p323 ∨ p10)
    (h26839 : p127 ∨ p6)
    (h26867 : p387 ∨ p303)
    (h19072 : (¬ p68) ∨ (¬ p127) ∨ (¬ p161) ∨ (¬ p323) ∨ (¬ p387) ∨ (¬ p864) ∨ (¬ p1147) ∨ (¬ p1508)) : (¬ p1147) ∨ (¬ p864) ∨ (¬ p161) ∨ p10 ∨ p6 ∨ (¬ p68) ∨ p303 ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1147 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19072 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u7)

theorem step27960 (p39 p63 p68 p101 p102 p121 p161 p211 p227 p1206 p1229 p1232 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26837 : p102 ∨ p101)
    (h26927 : p1232 ∨ p1229)
    (h17835 : (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p102) ∨ (¬ p161) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p1206) ∨ (¬ p1232)) : p121 ∨ (¬ p211) ∨ (¬ p227) ∨ p101 ∨ (¬ p63) ∨ (¬ p161) ∨ (¬ p68) ∨ p1229 ∨ (¬ p39) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p39 := by
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
    · exact False.elim (u3 q1)
  have u11 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h17835 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u11)

theorem step27961 (p15 p161 p1229 p1232 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26927 : p1232 ∨ p1229)
    (h16474 : (¬ p15) ∨ (¬ p161) ∨ (¬ p1232) ∨ (¬ p1333)) : p1325 ∨ p1229 ∨ (¬ p15) ∨ (¬ p161) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p161 := by
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
    · exact False.elim (u1 q1)
  rcases h16474 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step27962 (p6 p127 p161 p386 p1140 p1145 p1159 p1452 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26839 : p127 ∨ p6)
    (h17679 : (¬ p127) ∨ (¬ p161) ∨ (¬ p386) ∨ (¬ p1145) ∨ (¬ p1159) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p161) ∨ p1140 ∨ (¬ p1145) ∨ p6 ∨ (¬ p386) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1145 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p386 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17679 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u0)

theorem step27963 (p125 p160 p161 p163 p167 p236 p883 p1306 : Prop)
    (h26843 : p167 ∨ p163)
    (h20350 : (¬ p125) ∨ (¬ p160) ∨ (¬ p161) ∨ (¬ p167) ∨ (¬ p236) ∨ (¬ p883) ∨ (¬ p1306)) : (¬ p125) ∨ (¬ p160) ∨ (¬ p161) ∨ (¬ p1306) ∨ (¬ p236) ∨ (¬ p883) ∨ p163 := by
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
  have u3 : p1306 := by
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
  have u6 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20350 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u3)

theorem step27965 (p124 p161 p227 p304 p633 p665 p1082 p1229 p1232 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26859 : p304 ∨ p124)
    (h26927 : p1232 ∨ p1229)
    (h18822 : (¬ p161) ∨ (¬ p227) ∨ (¬ p304) ∨ (¬ p633) ∨ (¬ p665) ∨ (¬ p1082) ∨ (¬ p1232) ∨ (¬ p1333)) : p1325 ∨ p124 ∨ (¬ p665) ∨ (¬ p633) ∨ (¬ p161) ∨ p1229 ∨ (¬ p1082) ∨ (¬ p227) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1082 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18822 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u8)

theorem step27966 (p12 p104 p161 p344 p346 p980 p983 : Prop)
    (h26903 : p983 ∨ p980)
    (h26863 : p346 ∨ p344)
    (h16659 : (¬ p12) ∨ (¬ p104) ∨ (¬ p161) ∨ (¬ p346) ∨ (¬ p983)) : p980 ∨ (¬ p12) ∨ p344 ∨ (¬ p104) ∨ (¬ p161) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16659 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step27967 (p10 p161 p420 p457 p601 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26881 : p601 ∨ p420)
    (h18780 : (¬ p10) ∨ (¬ p161) ∨ (¬ p457) ∨ (¬ p601) ∨ (¬ p1333)) : (¬ p457) ∨ (¬ p10) ∨ (¬ p161) ∨ p1325 ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p457 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18780 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step27968 (p10 p25 p121 p161 p420 p601 p980 p983 p1081 p1147 : Prop)
    (h26881 : p601 ∨ p420)
    (h26903 : p983 ∨ p980)
    (h18809 : (¬ p10) ∨ (¬ p25) ∨ (¬ p121) ∨ (¬ p161) ∨ (¬ p601) ∨ (¬ p983) ∨ (¬ p1081) ∨ (¬ p1147)) : (¬ p1147) ∨ (¬ p10) ∨ (¬ p121) ∨ p420 ∨ (¬ p1081) ∨ (¬ p161) ∨ (¬ p25) ∨ p980 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1147 := by
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
  have u3 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p25 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18809 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u0)

theorem step27969 (p6 p121 p127 p161 p228 p1229 p1232 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26927 : p1232 ∨ p1229)
    (h26839 : p127 ∨ p6)
    (h25809 : (¬ p161) ∨ (¬ p1232) ∨ (¬ p121) ∨ (¬ p1333) ∨ (¬ p228) ∨ (¬ p127)) : p1325 ∨ (¬ p121) ∨ (¬ p161) ∨ (¬ p228) ∨ p1229 ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u8 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h25809 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u8)

theorem step27970 (p6 p121 p127 p161 p980 p983 p1081 p1229 p1232 : Prop)
    (h26903 : p983 ∨ p980)
    (h26927 : p1232 ∨ p1229)
    (h26839 : p127 ∨ p6)
    (h25810 : (¬ p1232) ∨ (¬ p161) ∨ (¬ p983) ∨ (¬ p127) ∨ (¬ p121) ∨ (¬ p1081)) : p980 ∨ (¬ p161) ∨ p1229 ∨ p6 ∨ (¬ p121) ∨ (¬ p1081) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25810 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)

theorem step27971 (p15 p49 p84 p161 p258 p266 p288 p1229 p1232 p1631 p1644 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h26855 : p288 ∨ p258)
    (h18203 : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p161) ∨ (¬ p266) ∨ (¬ p288) ∨ (¬ p1232) ∨ (¬ p1631) ∨ (¬ p1644)) : (¬ p1644) ∨ (¬ p84) ∨ (¬ p49) ∨ (¬ p15) ∨ (¬ p161) ∨ (¬ p266) ∨ p1229 ∨ p258 ∨ (¬ p1631) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1631 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18203 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u0)

theorem step27972 (p15 p161 p1035 p1229 p1232 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h21027 : (¬ p1035) ∨ (¬ p15) ∨ (¬ p161) ∨ (¬ p1232)) : (¬ p1035) ∨ p1229 ∨ (¬ p15) ∨ (¬ p161) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h21027 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step27974 (p124 p161 p344 p496 p728 p1229 p1232 p1330 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h19508 : (¬ p124) ∨ (¬ p161) ∨ (¬ p344) ∨ (¬ p496) ∨ (¬ p728) ∨ (¬ p1232) ∨ (¬ p1330)) : (¬ p728) ∨ (¬ p344) ∨ (¬ p161) ∨ (¬ p1330) ∨ p1229 ∨ (¬ p496) ∨ (¬ p124) := by
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
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19508 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step27975 (p124 p161 p496 p1035 p1044 p1076 p1077 p1229 p1232 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26927 : p1232 ∨ p1229)
    (h17489 : (¬ p124) ∨ (¬ p161) ∨ (¬ p496) ∨ (¬ p1035) ∨ (¬ p1044) ∨ (¬ p1077) ∨ (¬ p1232)) : p1076 ∨ (¬ p124) ∨ (¬ p496) ∨ (¬ p1035) ∨ p1229 ∨ (¬ p161) ∨ (¬ p1044) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : p124 := by
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
  have u4 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17489 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)

theorem step27978 (p124 p161 p227 p304 p367 p382 p633 p1292 p1442 p1508 : Prop)
    (h26859 : p304 ∨ p124)
    (h19231 : (¬ p161) ∨ (¬ p227) ∨ (¬ p304) ∨ (¬ p367) ∨ (¬ p382) ∨ (¬ p633) ∨ (¬ p1292) ∨ (¬ p1442) ∨ (¬ p1508)) : (¬ p1292) ∨ p124 ∨ (¬ p633) ∨ (¬ p367) ∨ (¬ p227) ∨ (¬ p161) ∨ (¬ p382) ∨ (¬ p1442) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1292 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p367 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p382 := by
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
  have u9 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19231 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u8)

theorem step27980 (p13 p41 p45 p158 p161 p918 p928 p1055 p1061 p1229 p1232 p1452 : Prop)
    (h26831 : p45 ∨ p41)
    (h26927 : p1232 ∨ p1229)
    (h26909 : p1061 ∨ p1055)
    (h26901 : p928 ∨ p918)
    (h20240 : (¬ p13) ∨ (¬ p45) ∨ (¬ p158) ∨ (¬ p161) ∨ (¬ p928) ∨ (¬ p1061) ∨ (¬ p1232) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p13) ∨ p41 ∨ p1229 ∨ p1055 ∨ (¬ p161) ∨ p918 ∨ (¬ p158) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20240 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u0)

theorem step27981 (p3 p161 p163 p226 p1140 p1229 p1232 p1258 p1508 : Prop)
    (h26847 : p226 ∨ p3)
    (h26927 : p1232 ∨ p1229)
    (h19278 : (¬ p161) ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p1140) ∨ (¬ p1232) ∨ (¬ p1258) ∨ (¬ p1508)) : (¬ p1258) ∨ (¬ p1140) ∨ (¬ p161) ∨ (¬ p163) ∨ p3 ∨ p1229 ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u8 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19278 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u6)

theorem step27982 (p3 p12 p161 p665 p1229 p1232 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26927 : p1232 ∨ p1229)
    (h25811 : (¬ p161) ∨ (¬ p1232) ∨ (¬ p12) ∨ (¬ p665) ∨ (¬ p3) ∨ (¬ p1333)) : p1325 ∨ (¬ p161) ∨ p1229 ∨ (¬ p3) ∨ (¬ p12) ∨ (¬ p665) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25811 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)

theorem step27983 (p3 p161 p225 p544 p728 p1229 p1232 p1330 : Prop)
    (h26877 : p544 ∨ p225)
    (h26927 : p1232 ∨ p1229)
    (h25812 : (¬ p1232) ∨ (¬ p161) ∨ (¬ p728) ∨ (¬ p544) ∨ (¬ p3) ∨ (¬ p1330)) : (¬ p728) ∨ p225 ∨ (¬ p1330) ∨ (¬ p161) ∨ p1229 ∨ (¬ p3) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25812 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u2)

theorem step27985 (p161 p495 p499 p980 p983 p1229 p1232 : Prop)
    (h26903 : p983 ∨ p980)
    (h26927 : p1232 ∨ p1229)
    (h26875 : p499 ∨ p495)
    (h20283 : (¬ p161) ∨ (¬ p499) ∨ (¬ p983) ∨ (¬ p1232)) : p980 ∨ p1229 ∨ p495 ∨ (¬ p161) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p161 := by
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
  have u6 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20283 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step27986 (p15 p161 p1229 p1232 p1452 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h19709 : (¬ p15) ∨ (¬ p161) ∨ (¬ p1232) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p161) ∨ (¬ p15) ∨ p1229 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19709 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step27987 (p161 p1225 p1292 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26924 : (¬ p161) ∨ (¬ p1225))
    (h10784 : p1225 ∨ (¬ p1292) ∨ (¬ p1333)) : p1325 ∨ (¬ p1292) ∨ (¬ p161) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : p1292 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : (¬ p1225) := by
    rcases h26924 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h10784 with q0 | q1 | q2
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step27993 (p11 p15 p39 p69 p88 p261 p1035 p1145 p1229 p1624 p1651 : Prop)
    (h26833 : p69 ∨ p15)
    (h19144 : (¬ p11) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p261) ∨ (¬ p1035) ∨ (¬ p1145) ∨ (¬ p1229) ∨ (¬ p1624) ∨ (¬ p1651)) : (¬ p1651) ∨ (¬ p1624) ∨ (¬ p11) ∨ (¬ p261) ∨ (¬ p88) ∨ (¬ p1145) ∨ (¬ p39) ∨ (¬ p1035) ∨ (¬ p1229) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1651 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1145 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h19144 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u1)
  · exact False.elim (q9 u0)

theorem step27994 (p18 p19 p67 p124 p161 p207 p533 p756 p1140 p1145 p1159 : Prop)
    (h26829 : p19 ∨ p18)
    (h26919 : p1159 ∨ p1140)
    (h17990 : (¬ p19) ∨ (¬ p67) ∨ (¬ p124) ∨ (¬ p161) ∨ (¬ p207) ∨ (¬ p533) ∨ (¬ p756) ∨ (¬ p1145) ∨ (¬ p1159)) : (¬ p756) ∨ (¬ p124) ∨ (¬ p161) ∨ (¬ p533) ∨ (¬ p1145) ∨ (¬ p207) ∨ (¬ p67) ∨ p18 ∨ p1140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1145 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h17990 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u10)

theorem step27995 (p15 p39 p69 p88 p185 p985 p1145 p1211 p1229 p1452 p1584 : Prop)
    (h26833 : p69 ∨ p15)
    (h19038 : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p185) ∨ (¬ p985) ∨ (¬ p1145) ∨ (¬ p1211) ∨ (¬ p1229) ∨ (¬ p1452) ∨ (¬ p1584)) : (¬ p1211) ∨ (¬ p1452) ∨ (¬ p39) ∨ p15 ∨ (¬ p88) ∨ (¬ p185) ∨ (¬ p1584) ∨ (¬ p1229) ∨ (¬ p985) ∨ (¬ p1145) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1145 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19038 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u1)
  · exact False.elim (q9 u6)

theorem step27998 (p423 p1141 p1147 p1149 p1150 p1151 p1152 p1153 : Prop)
    (h26916 : (¬ p423) ∨ (¬ p1141))
    (h6777 : p1141 ∨ p1147 ∨ (¬ p1149) ∨ (¬ p1150) ∨ (¬ p1151) ∨ (¬ p1152) ∨ (¬ p1153)) : p1147 ∨ (¬ p1150) ∨ (¬ p423) ∨ (¬ p1149) ∨ (¬ p1151) ∨ (¬ p1153) ∨ (¬ p1152) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1147) := fun hu => hn (Or.inl hu)
  have u1 : p1150 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1149 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1151 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1153 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1152 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p1141) := by
    rcases h26916 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h6777 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u5)

theorem step27999 (p423 p1141 p1148 p1149 p1150 p1151 p1152 p1153 : Prop)
    (h26916 : (¬ p423) ∨ (¬ p1141))
    (h6778 : p1141 ∨ p1148 ∨ (¬ p1149) ∨ (¬ p1150) ∨ (¬ p1151) ∨ (¬ p1152) ∨ (¬ p1153)) : p1148 ∨ (¬ p1150) ∨ (¬ p423) ∨ (¬ p1149) ∨ (¬ p1151) ∨ (¬ p1153) ∨ (¬ p1152) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1148) := fun hu => hn (Or.inl hu)
  have u1 : p1150 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1149 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1151 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1153 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1152 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p1141) := by
    rcases h26916 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h6778 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u5)

theorem step28010 (p861 p1325 p1333 p1489 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h10842 : (¬ p861) ∨ (¬ p1333) ∨ (¬ p1489)) : (¬ p861) ∨ (¬ p1489) ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p861 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h10842 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)

theorem step28011 (p41 p420 p434 p495 p499 p601 p1249 p1330 p1489 : Prop)
    (h26881 : p601 ∨ p420)
    (h26875 : p499 ∨ p495)
    (h17497 : (¬ p41) ∨ (¬ p434) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1249) ∨ (¬ p1330) ∨ (¬ p1489)) : (¬ p434) ∨ (¬ p1489) ∨ p420 ∨ p495 ∨ (¬ p41) ∨ (¬ p1330) ∨ (¬ p1249) := by
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
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17497 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u1)

theorem step28012 (p63 p85 p1249 p1325 p1333 p1489 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26835 : p85 ∨ p63)
    (h16847 : (¬ p85) ∨ (¬ p1249) ∨ (¬ p1333) ∨ (¬ p1489)) : (¬ p1489) ∨ p1325 ∨ (¬ p1249) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16847 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step28013 (p8 p14 p63 p85 p557 p728 p1249 p1330 p1489 : Prop)
    (h26835 : p85 ∨ p63)
    (h20209 : (¬ p8) ∨ (¬ p14) ∨ (¬ p85) ∨ (¬ p557) ∨ (¬ p728) ∨ (¬ p1249) ∨ (¬ p1330) ∨ (¬ p1489)) : (¬ p557) ∨ (¬ p728) ∨ (¬ p14) ∨ (¬ p1249) ∨ (¬ p8) ∨ (¬ p1489) ∨ (¬ p1330) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20209 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u5)

theorem step28014 (p17 p256 p386 p1349 p1452 p1489 : Prop)
    (h26853 : p256 ∨ p17)
    (h16831 : (¬ p256) ∨ (¬ p386) ∨ (¬ p1349) ∨ (¬ p1452) ∨ (¬ p1489)) : (¬ p386) ∨ (¬ p1452) ∨ (¬ p1349) ∨ p17 ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p386 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16831 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)

theorem step28015 (p285 p980 p983 p1076 p1077 p1489 : Prop)
    (h26903 : p983 ∨ p980)
    (h26911 : p1077 ∨ p1076)
    (h21913 : (¬ p1489) ∨ (¬ p983) ∨ (¬ p1077) ∨ (¬ p285)) : (¬ p1489) ∨ p980 ∨ p1076 ∨ (¬ p285) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p285 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h21913 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)

theorem step28016 (p63 p85 p124 p496 p533 p756 p1249 p1489 : Prop)
    (h26835 : p85 ∨ p63)
    (h18020 : (¬ p85) ∨ (¬ p124) ∨ (¬ p496) ∨ (¬ p533) ∨ (¬ p756) ∨ (¬ p1249) ∨ (¬ p1489)) : (¬ p756) ∨ (¬ p124) ∨ p63 ∨ (¬ p533) ∨ (¬ p496) ∨ (¬ p1489) ∨ (¬ p1249) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18020 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u5)

theorem step28017 (p185 p237 p918 p1349 p1489 : Prop)
    (h26851 : p237 ∨ p185)
    (h18620 : (¬ p237) ∨ (¬ p918) ∨ (¬ p1349) ∨ (¬ p1489)) : (¬ p1349) ∨ p185 ∨ (¬ p1489) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18620 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)

theorem step28018 (p3 p63 p85 p533 p534 p1249 p1489 : Prop)
    (h26835 : p85 ∨ p63)
    (h25813 : (¬ p1249) ∨ (¬ p534) ∨ (¬ p533) ∨ (¬ p3) ∨ (¬ p85) ∨ (¬ p1489)) : (¬ p534) ∨ p63 ∨ (¬ p533) ∨ (¬ p1249) ∨ (¬ p3) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25813 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)

theorem step28019 (p63 p85 p125 p362 p434 p496 p1249 p1330 p1489 : Prop)
    (h26865 : p362 ∨ p125)
    (h26835 : p85 ∨ p63)
    (h17527 : (¬ p85) ∨ (¬ p362) ∨ (¬ p434) ∨ (¬ p496) ∨ (¬ p1249) ∨ (¬ p1330) ∨ (¬ p1489)) : (¬ p434) ∨ (¬ p496) ∨ (¬ p1489) ∨ p125 ∨ (¬ p1249) ∨ p63 ∨ (¬ p1330) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17527 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u2)

theorem step28020 (p83 p185 p918 p928 p1249 p1489 : Prop)
    (h26901 : p928 ∨ p918)
    (h19901 : (¬ p83) ∨ (¬ p185) ∨ (¬ p928) ∨ (¬ p1249) ∨ (¬ p1489)) : p918 ∨ (¬ p1249) ∨ (¬ p83) ∨ (¬ p185) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p918) := fun hu => hn (Or.inl hu)
  have u1 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19901 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)

theorem step28021 (p8 p63 p85 p101 p102 p306 p728 p1249 p1330 p1489 : Prop)
    (h26835 : p85 ∨ p63)
    (h26837 : p102 ∨ p101)
    (h18505 : (¬ p8) ∨ (¬ p85) ∨ (¬ p102) ∨ (¬ p306) ∨ (¬ p728) ∨ (¬ p1249) ∨ (¬ p1330) ∨ (¬ p1489)) : (¬ p306) ∨ (¬ p728) ∨ (¬ p1249) ∨ (¬ p1489) ∨ p63 ∨ (¬ p1330) ∨ (¬ p8) ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18505 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u3)

theorem step28022 (p8 p258 p264 p288 p305 p344 p710 : Prop)
    (h26889 : p710 ∨ p8)
    (h26855 : p288 ∨ p258)
    (h20055 : (¬ p264) ∨ (¬ p288) ∨ (¬ p305) ∨ (¬ p344) ∨ (¬ p710)) : (¬ p305) ∨ (¬ p344) ∨ p8 ∨ (¬ p264) ∨ p258 := by
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
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p264 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20055 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)

theorem step28023 (p160 p980 p983 p1060 : Prop)
    (h26903 : p983 ∨ p980)
    (h12489 : p160 ∨ (¬ p983) ∨ (¬ p1060)) : (¬ p1060) ∨ p980 ∨ p160 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1060 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p160) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h12489 with q0 | q1 | q2
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)

theorem step28028 (p12 p557 p1036 p1055 : Prop)
    (h26907 : p1036 ∨ p12)
    (h14961 : (¬ p557) ∨ (¬ p1036) ∨ p1055) : (¬ p557) ∨ p1055 ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p12) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h14961 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)

theorem step28033 (p11 p258 p344 p346 p668 p1082 p1443 : Prop)
    (h26863 : p346 ∨ p344)
    (h26935 : p1443 ∨ p11)
    (h20509 : (¬ p258) ∨ (¬ p346) ∨ (¬ p668) ∨ (¬ p1082) ∨ (¬ p1443)) : (¬ p258) ∨ p344 ∨ p11 ∨ (¬ p1082) ∨ (¬ p668) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1082 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20509 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)

theorem step28037 (p3 p110 p226 p1041 p1076 p1140 : Prop)
    (h26847 : p226 ∨ p3)
    (h16263 : (¬ p110) ∨ (¬ p226) ∨ (¬ p1041) ∨ (¬ p1076) ∨ (¬ p1140)) : (¬ p1140) ∨ (¬ p110) ∨ (¬ p1041) ∨ p3 ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1041 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16263 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)

theorem step28038 (p14 p110 p229 p423 p1041 p1076 : Prop)
    (h26849 : p229 ∨ p14)
    (h18274 : (¬ p110) ∨ (¬ p229) ∨ (¬ p423) ∨ (¬ p1041) ∨ (¬ p1076)) : (¬ p423) ∨ p14 ∨ (¬ p110) ∨ (¬ p1076) ∨ (¬ p1041) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p14) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1041 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18274 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)

theorem step28040 (p12 p172 p918 p1036 p1121 p1273 : Prop)
    (h26907 : p1036 ∨ p12)
    (h20179 : (¬ p172) ∨ (¬ p918) ∨ (¬ p1036) ∨ (¬ p1121) ∨ (¬ p1273)) : (¬ p172) ∨ (¬ p1273) ∨ p12 ∨ (¬ p918) ∨ (¬ p1121) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20179 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)

theorem step28052 (p67 p234 p382 p419 p477 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h16884 : (¬ p67) ∨ (¬ p234) ∨ (¬ p382) ∨ (¬ p477) ∨ (¬ p996)) : (¬ p382) ∨ p419 ∨ (¬ p234) ∨ (¬ p67) ∨ (¬ p477) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p477 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16884 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step28054 (p15 p125 p224 p234 p303 p542 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h25815 : (¬ p303) ∨ (¬ p125) ∨ (¬ p234) ∨ (¬ p15) ∨ (¬ p657) ∨ (¬ p542)) : (¬ p542) ∨ (¬ p125) ∨ (¬ p303) ∨ (¬ p234) ∨ p224 ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25815 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u0)

theorem step28055 (p15 p125 p234 p419 p431 p438 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h25816 : (¬ p125) ∨ (¬ p15) ∨ (¬ p438) ∨ (¬ p996) ∨ (¬ p431) ∨ (¬ p234)) : (¬ p431) ∨ p419 ∨ (¬ p125) ∨ (¬ p15) ∨ (¬ p438) ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25816 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u5)

theorem step28056 (p8 p15 p234 p419 p431 p710 p734 p996 p1103 : Prop)
    (h26889 : p710 ∨ p8)
    (h26905 : p996 ∨ p419)
    (h20431 : (¬ p15) ∨ (¬ p234) ∨ (¬ p431) ∨ (¬ p710) ∨ (¬ p734) ∨ (¬ p996) ∨ (¬ p1103)) : (¬ p734) ∨ (¬ p431) ∨ p8 ∨ p419 ∨ (¬ p15) ∨ (¬ p1103) ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p419) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20431 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u5)

theorem step28057 (p234 p423 p1141 p1325 p1333 p1465 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26931 : p1333 ∨ p1325)
    (h19203 : (¬ p234) ∨ (¬ p1141) ∨ (¬ p1333) ∨ (¬ p1465)) : p423 ∨ p1325 ∨ (¬ p234) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
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
  rcases h19203 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)

theorem step28060 (p48 p156 p234 p424 p796 p918 : Prop)
    (h26891 : p796 ∨ p424)
    (h18617 : (¬ p48) ∨ (¬ p156) ∨ (¬ p234) ∨ (¬ p796) ∨ (¬ p918)) : (¬ p156) ∨ p424 ∨ (¬ p48) ∨ (¬ p234) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p424) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18617 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)

theorem step28061 (p15 p234 p542 p836 p1055 p1103 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h19913 : (¬ p15) ∨ (¬ p234) ∨ (¬ p542) ∨ (¬ p836) ∨ (¬ p1055) ∨ (¬ p1103) ∨ (¬ p1116)) : p1115 ∨ (¬ p836) ∨ (¬ p1055) ∨ (¬ p234) ∨ (¬ p542) ∨ (¬ p15) ∨ (¬ p1103) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1115) := fun hu => hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h19913 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step28063 (p124 p135 p234 p265 p304 p344 p346 p422 p423 p542 p1141 p1256 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26859 : p304 ∨ p124)
    (h26929 : p1256 ∨ p422)
    (h26863 : p346 ∨ p344)
    (h20081 : (¬ p135) ∨ (¬ p234) ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p542) ∨ (¬ p1141) ∨ (¬ p1256)) : p423 ∨ p124 ∨ (¬ p135) ∨ (¬ p542) ∨ p422 ∨ (¬ p234) ∨ p344 ∨ (¬ p265) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20081 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u10)

theorem step28064 (p15 p63 p85 p124 p234 p304 p344 p346 p425 p542 p582 : Prop)
    (h26859 : p304 ∨ p124)
    (h26835 : p85 ∨ p63)
    (h26863 : p346 ∨ p344)
    (h16542 : (¬ p15) ∨ (¬ p85) ∨ (¬ p234) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p425) ∨ (¬ p542) ∨ (¬ p582)) : (¬ p425) ∨ p124 ∨ (¬ p582) ∨ (¬ p542) ∨ (¬ p15) ∨ p63 ∨ p344 ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h16542 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u2)

theorem step28066 (p18 p101 p224 p234 p543 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h17080 : (¬ p18) ∨ (¬ p101) ∨ (¬ p234) ∨ (¬ p543) ∨ (¬ p657)) : (¬ p543) ∨ (¬ p101) ∨ p224 ∨ (¬ p18) ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p543 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17080 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step28075 (p234 p1187 p1195 p1201 p1202 p1203 p1204 p1205 : Prop)
    (h26920 : (¬ p234) ∨ (¬ p1187))
    (h7102 : p1187 ∨ p1195 ∨ (¬ p1201) ∨ (¬ p1202) ∨ (¬ p1203) ∨ (¬ p1204) ∨ (¬ p1205)) : (¬ p1205) ∨ p1195 ∨ (¬ p234) ∨ (¬ p1202) ∨ (¬ p1201) ∨ (¬ p1204) ∨ (¬ p1203) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1205 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1195) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1202 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1201 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1204 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1203 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p1187) := by
    rcases h26920 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h7102 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u0)

theorem step28076 (p41 p45 p797 p1385 : Prop)
    (h26831 : p45 ∨ p41)
    (h13514 : (¬ p45) ∨ (¬ p797) ∨ p1385) : (¬ p797) ∨ p1385 ∨ p41 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p797 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h13514 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (u1 q2)

theorem step28077 (p41 p1249 p1325 p1333 p1489 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h18317 : (¬ p41) ∨ (¬ p1249) ∨ (¬ p1333) ∨ (¬ p1489)) : p1325 ∨ (¬ p1249) ∨ (¬ p1489) ∨ (¬ p41) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18317 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step28078 (p63 p85 p86 p1249 p1346 : Prop)
    (h26835 : p85 ∨ p63)
    (h16321 : (¬ p85) ∨ (¬ p86) ∨ (¬ p1249) ∨ (¬ p1346)) : (¬ p1346) ∨ (¬ p1249) ∨ p63 ∨ (¬ p86) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16321 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)

theorem step28080 (p121 p576 p581 p1249 p1493 : Prop)
    (h26879 : p581 ∨ p576)
    (h22715 : (¬ p1493) ∨ (¬ p581) ∨ (¬ p121) ∨ (¬ p1249)) : (¬ p1493) ∨ (¬ p1249) ∨ p576 ∨ (¬ p121) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1493 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h22715 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)

theorem step28081 (p576 p581 p1249 p1496 : Prop)
    (h26879 : p581 ∨ p576)
    (h11686 : (¬ p581) ∨ (¬ p1249) ∨ (¬ p1496)) : (¬ p1249) ∨ p576 ∨ (¬ p1496) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h11686 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)

theorem step28082 (p532 p576 p581 p1249 p1325 p1333 p1493 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26879 : p581 ∨ p576)
    (h19104 : (¬ p532) ∨ (¬ p581) ∨ (¬ p1249) ∨ (¬ p1333) ∨ (¬ p1493)) : (¬ p1249) ∨ p1325 ∨ (¬ p532) ∨ p576 ∨ (¬ p1493) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1493 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19104 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)

theorem step28083 (p258 p288 p576 p581 p1080 p1249 p1493 : Prop)
    (h26879 : p581 ∨ p576)
    (h26855 : p288 ∨ p258)
    (h17072 : (¬ p288) ∨ (¬ p581) ∨ (¬ p1080) ∨ (¬ p1249) ∨ (¬ p1493)) : (¬ p1493) ∨ (¬ p1249) ∨ p576 ∨ (¬ p1080) ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1493 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17072 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step28084 (p17 p41 p189 p256 p1249 : Prop)
    (h26853 : p256 ∨ p17)
    (h17106 : (¬ p41) ∨ (¬ p189) ∨ (¬ p256) ∨ (¬ p1249)) : p17 ∨ (¬ p41) ∨ (¬ p189) ∨ (¬ p1249) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p17) := fun hu => hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17106 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)

theorem step28085 (p17 p423 p576 p581 p864 p1035 p1249 p1325 : Prop)
    (h26879 : p581 ∨ p576)
    (h20213 : (¬ p17) ∨ (¬ p423) ∨ (¬ p581) ∨ (¬ p864) ∨ (¬ p1035) ∨ (¬ p1249) ∨ (¬ p1325)) : (¬ p864) ∨ (¬ p1035) ∨ p576 ∨ (¬ p1325) ∨ (¬ p17) ∨ (¬ p1249) ∨ (¬ p423) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20213 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u3)

theorem step28086 (p244 p918 p928 p1055 p1061 p1118 p1249 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26901 : p928 ∨ p918)
    (h18315 : (¬ p244) ∨ (¬ p928) ∨ (¬ p1061) ∨ (¬ p1118) ∨ (¬ p1249)) : (¬ p1118) ∨ p1055 ∨ (¬ p1249) ∨ p918 ∨ (¬ p244) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1118 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p244 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18315 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u2)

theorem step28089 (p41 p83 p125 p189 p303 p362 p387 p496 p864 p1249 : Prop)
    (h26867 : p387 ∨ p303)
    (h26865 : p362 ∨ p125)
    (h17161 : (¬ p41) ∨ (¬ p83) ∨ (¬ p189) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p496) ∨ (¬ p864) ∨ (¬ p1249)) : (¬ p864) ∨ (¬ p1249) ∨ (¬ p496) ∨ (¬ p189) ∨ (¬ p83) ∨ (¬ p41) ∨ p303 ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h17161 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u1)

theorem step28090 (p3 p14 p83 p226 p790 p814 p1140 p1249 p1258 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h26893 : p814 ∨ p790)
    (h26847 : p226 ∨ p3)
    (h19270 : (¬ p14) ∨ (¬ p83) ∨ (¬ p226) ∨ (¬ p814) ∨ (¬ p1140) ∨ (¬ p1249) ∨ (¬ p1258) ∨ (¬ p1393)) : (¬ p1258) ∨ (¬ p1140) ∨ p1385 ∨ (¬ p1249) ∨ p790 ∨ p3 ∨ (¬ p14) ∨ (¬ p83) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19270 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u8)

theorem step28091 (p3 p63 p85 p224 p225 p544 p657 p864 p1249 : Prop)
    (h26877 : p544 ∨ p225)
    (h26835 : p85 ∨ p63)
    (h26887 : p657 ∨ p224)
    (h25818 : (¬ p864) ∨ (¬ p1249) ∨ (¬ p85) ∨ (¬ p544) ∨ (¬ p657) ∨ (¬ p3)) : (¬ p864) ∨ p225 ∨ p63 ∨ (¬ p1249) ∨ (¬ p3) ∨ p224 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h25818 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)

theorem step28093 (p63 p85 p864 p980 p983 p1055 p1061 p1249 p1325 : Prop)
    (h26903 : p983 ∨ p980)
    (h26835 : p85 ∨ p63)
    (h26909 : p1061 ∨ p1055)
    (h22716 : (¬ p864) ∨ (¬ p983) ∨ (¬ p1249) ∨ (¬ p1325) ∨ (¬ p85) ∨ (¬ p1061)) : (¬ p864) ∨ p980 ∨ (¬ p1249) ∨ p63 ∨ p1055 ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h22716 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)

theorem step28094 (p6 p10 p39 p68 p127 p323 p434 p1249 p1330 p1489 : Prop)
    (h26861 : p323 ∨ p10)
    (h26839 : p127 ∨ p6)
    (h19073 : (¬ p39) ∨ (¬ p68) ∨ (¬ p127) ∨ (¬ p323) ∨ (¬ p434) ∨ (¬ p1249) ∨ (¬ p1330) ∨ (¬ p1489)) : (¬ p434) ∨ (¬ p1489) ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p1330) ∨ (¬ p1249) ∨ p10 ∨ p6 := by
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
  have u2 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19073 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u1)

theorem step28095 (p790 p814 p856 p1346 : Prop)
    (h26893 : p814 ∨ p790)
    (h13653 : (¬ p814) ∨ (¬ p856) ∨ (¬ p1346)) : (¬ p856) ∨ (¬ p1346) ∨ p790 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p856 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p790) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h13653 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)

theorem step28099 (p17 p256 p532 p790 p814 p856 p1325 p1333 p1493 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26893 : p814 ∨ p790)
    (h26853 : p256 ∨ p17)
    (h19224 : (¬ p256) ∨ (¬ p532) ∨ (¬ p814) ∨ (¬ p856) ∨ (¬ p1333) ∨ (¬ p1493)) : (¬ p856) ∨ p1325 ∨ p790 ∨ p17 ∨ (¬ p532) ∨ (¬ p1493) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p856 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1493 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19224 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)

theorem step28100 (p856 p1273 p1385 p1393 : Prop)
    (h26932 : (¬ p1385) ∨ (¬ p1393))
    (h12306 : (¬ p856) ∨ (¬ p1273) ∨ p1393) : (¬ p856) ∨ (¬ p1273) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p856 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1393) := by
    rcases h26932 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h12306 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u3 q2)

theorem step28101 (p41 p795 p1385 p1393 : Prop)
    (h26932 : (¬ p1385) ∨ (¬ p1393))
    (h12631 : (¬ p41) ∨ (¬ p795) ∨ p1393) : (¬ p1385) ∨ (¬ p41) ∨ (¬ p795) := by
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
  have u2 : p795 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1393) := by
    rcases h26932 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  rcases h12631 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (u3 q2)

theorem step28102 (p72 p160 p423 p1141 p1168 p1465 : Prop)
    (h26917 : p1141 ∨ p423)
    (h18063 : (¬ p72) ∨ (¬ p160) ∨ (¬ p1141) ∨ (¬ p1168) ∨ (¬ p1465)) : (¬ p1168) ∨ (¬ p160) ∨ p423 ∨ (¬ p1465) ∨ (¬ p72) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1168 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p423) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18063 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)

theorem step28105 (p18 p19 p63 p85 p160 p207 p228 p236 p532 p789 p858 p1385 : Prop)
    (h26829 : p19 ∨ p18)
    (h26897 : p858 ∨ p789)
    (h26835 : p85 ∨ p63)
    (h19896 : (¬ p19) ∨ (¬ p85) ∨ (¬ p160) ∨ (¬ p207) ∨ (¬ p228) ∨ (¬ p236) ∨ (¬ p532) ∨ (¬ p858) ∨ (¬ p1385)) : p18 ∨ (¬ p160) ∨ p789 ∨ (¬ p1385) ∨ (¬ p532) ∨ (¬ p228) ∨ p63 ∨ (¬ p207) ∨ (¬ p236) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p18) := fun hu => hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p236 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19896 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u3)

theorem step28108 (p595 p635 p664 p902 p1076 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h16487 : (¬ p595) ∨ (¬ p635) ∨ (¬ p664) ∨ (¬ p902) ∨ (¬ p1076) ∨ (¬ p1099)) : (¬ p635) ∨ p1096 ∨ (¬ p902) ∨ (¬ p1076) ∨ (¬ p595) ∨ (¬ p664) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p635 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p902 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16487 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)

theorem step28109 (p344 p635 p897 p904 : Prop)
    (h26899 : p904 ∨ p897)
    (h11229 : p344 ∨ (¬ p635) ∨ (¬ p904)) : (¬ p635) ∨ p897 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p635 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h11229 with q0 | q1 | q2
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)

theorem step28110 (p344 p346 p635 p897 : Prop)
    (h26863 : p346 ∨ p344)
    (h15754 : (¬ p346) ∨ (¬ p635) ∨ p897) : (¬ p635) ∨ p897 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p635 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h15754 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (u1 q2)

theorem step28111 (p258 p288 p595 p635 p1096 p1099 p1286 : Prop)
    (h26855 : p288 ∨ p258)
    (h26913 : p1099 ∨ p1096)
    (h20485 : (¬ p288) ∨ (¬ p595) ∨ (¬ p635) ∨ (¬ p1099) ∨ (¬ p1286)) : (¬ p635) ∨ (¬ p1286) ∨ p258 ∨ (¬ p595) ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p635 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20485 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)

theorem step28113 (p121 p160 p161 p897 p904 p960 p1306 : Prop)
    (h26899 : p904 ∨ p897)
    (h19949 : (¬ p121) ∨ (¬ p160) ∨ (¬ p161) ∨ (¬ p904) ∨ (¬ p960) ∨ (¬ p1306)) : (¬ p960) ∨ (¬ p1306) ∨ (¬ p121) ∨ p897 ∨ (¬ p161) ∨ (¬ p160) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p960 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19949 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u1)

theorem step28114 (p89 p185 p237 p923 p1096 : Prop)
    (h26851 : p237 ∨ p185)
    (h12072 : (¬ p89) ∨ (¬ p237) ∨ (¬ p923) ∨ p1096) : (¬ p923) ∨ p185 ∨ (¬ p89) ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p923 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h12072 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (u3 q3)

theorem step28117 (p101 p102 p897 p904 p1074 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26837 : p102 ∨ p101)
    (h26899 : p904 ∨ p897)
    (h16625 : (¬ p102) ∨ (¬ p904) ∨ (¬ p1074) ∨ (¬ p1077)) : p1076 ∨ (¬ p1074) ∨ p101 ∨ p897 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16625 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step28118 (p836 p897 p904 p923 : Prop)
    (h26899 : p904 ∨ p897)
    (h11921 : (¬ p836) ∨ (¬ p904) ∨ (¬ p923)) : (¬ p836) ∨ p897 ∨ (¬ p923) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p923 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h11921 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)

theorem step28119 (p224 p657 p897 p904 p1096 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26887 : p657 ∨ p224)
    (h26899 : p904 ∨ p897)
    (h17475 : (¬ p657) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1333)) : p1325 ∨ p224 ∨ p897 ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17475 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step28120 (p344 p346 p897 p904 p980 p1074 : Prop)
    (h26899 : p904 ∨ p897)
    (h26863 : p346 ∨ p344)
    (h18037 : (¬ p346) ∨ (¬ p904) ∨ (¬ p980) ∨ (¬ p1074)) : (¬ p1074) ∨ p897 ∨ p344 ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18037 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)

theorem step28121 (p344 p346 p897 p904 p1076 p1077 p1096 : Prop)
    (h26863 : p346 ∨ p344)
    (h26911 : p1077 ∨ p1076)
    (h26899 : p904 ∨ p897)
    (h18395 : (¬ p346) ∨ (¬ p904) ∨ (¬ p1077) ∨ (¬ p1096)) : p344 ∨ p1076 ∨ p897 ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p344) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18395 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)

theorem step28123 (p836 p897 p904 p1096 p1115 p1116 : Prop)
    (h26899 : p904 ∨ p897)
    (h26915 : p1116 ∨ p1115)
    (h20439 : (¬ p836) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1116)) : (¬ p836) ∨ (¬ p1096) ∨ p897 ∨ p1115 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20439 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)

theorem step28124 (p12 p225 p897 p904 p1096 : Prop)
    (h26899 : p904 ∨ p897)
    (h20520 : (¬ p12) ∨ (¬ p225) ∨ (¬ p904) ∨ (¬ p1096)) : p897 ∨ (¬ p225) ∨ (¬ p12) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p897) := fun hu => hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h20520 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)

theorem step28125 (p15 p69 p344 p346 p897 p904 p1096 : Prop)
    (h26899 : p904 ∨ p897)
    (h26863 : p346 ∨ p344)
    (h26833 : p69 ∨ p15)
    (h19088 : (¬ p69) ∨ (¬ p346) ∨ (¬ p904) ∨ (¬ p1096)) : (¬ p1096) ∨ p897 ∨ p344 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19088 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step28126 (p15 p69 p225 p897 p904 p1096 : Prop)
    (h26899 : p904 ∨ p897)
    (h26833 : p69 ∨ p15)
    (h19361 : (¬ p69) ∨ (¬ p225) ∨ (¬ p904) ∨ (¬ p1096)) : (¬ p1096) ∨ p897 ∨ (¬ p225) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19361 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step28127 (p63 p85 p225 p897 p904 p1096 : Prop)
    (h26899 : p904 ∨ p897)
    (h26835 : p85 ∨ p63)
    (h16521 : (¬ p85) ∨ (¬ p225) ∨ (¬ p904) ∨ (¬ p1096)) : (¬ p1096) ∨ p897 ∨ p63 ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16521 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step28128 (p63 p85 p836 p897 p904 p1096 : Prop)
    (h26899 : p904 ∨ p897)
    (h26835 : p85 ∨ p63)
    (h16621 : (¬ p85) ∨ (¬ p836) ∨ (¬ p904) ∨ (¬ p1096)) : (¬ p1096) ∨ (¬ p836) ∨ p897 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16621 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step28129 (p225 p880 p897 p904 : Prop)
    (h26899 : p904 ∨ p897)
    (h11737 : (¬ p225) ∨ (¬ p880) ∨ (¬ p904)) : (¬ p880) ∨ p897 ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h11737 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)

theorem step28130 (p101 p102 p756 p897 p904 p1538 : Prop)
    (h26837 : p102 ∨ p101)
    (h26899 : p904 ∨ p897)
    (h16632 : (¬ p102) ∨ (¬ p756) ∨ (¬ p904) ∨ (¬ p1538)) : (¬ p756) ∨ p101 ∨ (¬ p1538) ∨ p897 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16632 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)

theorem step28131 (p163 p557 p897 p904 p1055 p1061 p1074 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26899 : p904 ∨ p897)
    (h19133 : (¬ p163) ∨ (¬ p557) ∨ (¬ p904) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p1074) ∨ p1055 ∨ (¬ p163) ∨ p897 ∨ (¬ p557) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19133 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step28135 (p5 p6 p121 p224 p389 p657 p897 p904 p1096 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26899 : p904 ∨ p897)
    (h26887 : p657 ∨ p224)
    (h19999 : (¬ p5) ∨ (¬ p6) ∨ (¬ p389) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1206)) : (¬ p389) ∨ p121 ∨ p897 ∨ (¬ p5) ∨ p224 ∨ (¬ p1096) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19999 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)

theorem step28136 (p8 p63 p710 p897 p904 p924 p1097 : Prop)
    (h26899 : p904 ∨ p897)
    (h26889 : p710 ∨ p8)
    (h18157 : (¬ p63) ∨ (¬ p710) ∨ (¬ p904) ∨ (¬ p924) ∨ (¬ p1097)) : p897 ∨ (¬ p1097) ∨ (¬ p63) ∨ (¬ p924) ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p897) := fun hu => hn (Or.inl hu)
  have u1 : p1097 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18157 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)

theorem step28137 (p4 p126 p258 p288 p301 p642 p897 p904 : Prop)
    (h26857 : p301 ∨ p126)
    (h26855 : p288 ∨ p258)
    (h26899 : p904 ∨ p897)
    (h17110 : (¬ p4) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p642) ∨ (¬ p904)) : p126 ∨ (¬ p4) ∨ p258 ∨ p897 ∨ (¬ p642) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p642 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17110 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)

theorem step28138 (p11 p224 p258 p657 p897 p904 p961 p1096 p1443 : Prop)
    (h26887 : p657 ∨ p224)
    (h26899 : p904 ∨ p897)
    (h26935 : p1443 ∨ p11)
    (h25819 : (¬ p961) ∨ (¬ p1443) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p258) ∨ (¬ p657)) : (¬ p961) ∨ (¬ p258) ∨ p224 ∨ (¬ p1096) ∨ p897 ∨ p11 := by
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
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u8 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h25819 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)

theorem step28139 (p103 p225 p423 p884 p897 p904 p1141 p1209 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26899 : p904 ∨ p897)
    (h18768 : (¬ p103) ∨ (¬ p225) ∨ (¬ p884) ∨ (¬ p904) ∨ (¬ p1141) ∨ (¬ p1209)) : (¬ p103) ∨ (¬ p884) ∨ p423 ∨ (¬ p225) ∨ (¬ p1209) ∨ p897 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p884 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p423) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18768 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u4)

theorem step28140 (p41 p45 p189 p193 p836 p897 p904 p927 : Prop)
    (h26845 : p193 ∨ p189)
    (h26831 : p45 ∨ p41)
    (h26899 : p904 ∨ p897)
    (h17359 : (¬ p45) ∨ (¬ p193) ∨ (¬ p836) ∨ (¬ p904) ∨ (¬ p927)) : p189 ∨ p41 ∨ p897 ∨ (¬ p927) ∨ (¬ p836) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p189) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17359 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u3)

theorem step28141 (p5 p6 p101 p664 p897 p904 p1076 p1096 : Prop)
    (h26899 : p904 ∨ p897)
    (h16622 : (¬ p5) ∨ (¬ p6) ∨ (¬ p101) ∨ (¬ p664) ∨ (¬ p904) ∨ (¬ p1076) ∨ (¬ p1096)) : (¬ p101) ∨ (¬ p1076) ∨ p897 ∨ (¬ p6) ∨ (¬ p1096) ∨ (¬ p664) ∨ (¬ p5) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16622 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u4)

theorem step28142 (p156 p189 p193 p728 p897 p904 p923 p1330 p1349 p1489 : Prop)
    (h26899 : p904 ∨ p897)
    (h26845 : p193 ∨ p189)
    (h18455 : (¬ p156) ∨ (¬ p193) ∨ (¬ p728) ∨ (¬ p904) ∨ (¬ p923) ∨ (¬ p1330) ∨ (¬ p1349) ∨ (¬ p1489)) : p897 ∨ (¬ p1349) ∨ (¬ p156) ∨ (¬ p1489) ∨ (¬ p1330) ∨ (¬ p923) ∨ (¬ p728) ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p897) := fun hu => hn (Or.inl hu)
  have u1 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p923 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18455 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u3)

theorem step28143 (p17 p224 p256 p576 p657 p864 p897 p904 p1096 p1349 : Prop)
    (h26853 : p256 ∨ p17)
    (h26899 : p904 ∨ p897)
    (h26887 : p657 ∨ p224)
    (h20534 : (¬ p256) ∨ (¬ p576) ∨ (¬ p657) ∨ (¬ p864) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1349)) : (¬ p864) ∨ (¬ p1096) ∨ (¬ p576) ∨ p17 ∨ p897 ∨ p224 ∨ (¬ p1349) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20534 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u6)

theorem step28146 (p63 p85 p224 p657 p897 p904 p1096 : Prop)
    (h26899 : p904 ∨ p897)
    (h26887 : p657 ∨ p224)
    (h26835 : p85 ∨ p63)
    (h16561 : (¬ p85) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1096)) : (¬ p1096) ∨ p897 ∨ p224 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16561 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step28147 (p6 p10 p38 p49 p63 p85 p351 p897 p904 p1096 : Prop)
    (h26835 : p85 ∨ p63)
    (h26899 : p904 ∨ p897)
    (h16624 : (¬ p6) ∨ (¬ p10) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p351) ∨ (¬ p904) ∨ (¬ p1096)) : (¬ p38) ∨ (¬ p10) ∨ p63 ∨ (¬ p351) ∨ (¬ p49) ∨ (¬ p6) ∨ (¬ p1096) ∨ p897 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h16624 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u6)

theorem step28148 (p11 p16 p17 p224 p389 p657 p897 p904 p1096 : Prop)
    (h26899 : p904 ∨ p897)
    (h26887 : p657 ∨ p224)
    (h20511 : (¬ p11) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p389) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1096)) : (¬ p11) ∨ (¬ p389) ∨ p897 ∨ (¬ p16) ∨ p224 ∨ (¬ p17) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20511 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u6)

theorem step28149 (p2 p5 p224 p431 p435 p657 p897 p904 p1096 : Prop)
    (h26887 : p657 ∨ p224)
    (h26899 : p904 ∨ p897)
    (h17501 : (¬ p2) ∨ (¬ p5) ∨ (¬ p431) ∨ (¬ p435) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1096)) : (¬ p2) ∨ (¬ p1096) ∨ (¬ p5) ∨ (¬ p431) ∨ p224 ∨ (¬ p435) ∨ p897 := by
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
  have u2 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u8 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17501 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u1)

theorem step28151 (p5 p728 p897 p904 p1096 p1140 p1159 p1330 p1465 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26899 : p904 ∨ p897)
    (h17499 : (¬ p5) ∨ (¬ p728) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1159) ∨ (¬ p1330) ∨ (¬ p1465)) : p1140 ∨ (¬ p1465) ∨ (¬ p5) ∨ (¬ p1330) ∨ (¬ p728) ∨ (¬ p1096) ∨ p897 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17499 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u1)

theorem step28153 (p16 p134 p188 p224 p422 p657 p897 p904 p1096 p1140 p1159 p1256 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26899 : p904 ∨ p897)
    (h26887 : p657 ∨ p224)
    (h26929 : p1256 ∨ p422)
    (h18443 : (¬ p16) ∨ (¬ p134) ∨ (¬ p188) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1159) ∨ (¬ p1256)) : p1140 ∨ p897 ∨ (¬ p16) ∨ (¬ p1096) ∨ (¬ p188) ∨ p224 ∨ (¬ p134) ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18443 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u11)

theorem step28154 (p41 p45 p90 p101 p102 p124 p185 p192 p206 p224 p237 p304 p657 p897 p904 p923 : Prop)
    (h26899 : p904 ∨ p897)
    (h26837 : p102 ∨ p101)
    (h26887 : p657 ∨ p224)
    (h26851 : p237 ∨ p185)
    (h26831 : p45 ∨ p41)
    (h26859 : p304 ∨ p124)
    (h26586 : p90)
    (h20618 : (¬ p45) ∨ (¬ p90) ∨ (¬ p102) ∨ (¬ p192) ∨ (¬ p206) ∨ (¬ p237) ∨ (¬ p304) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p923)) : (¬ p923) ∨ (¬ p192) ∨ p897 ∨ p101 ∨ p224 ∨ (¬ p206) ∨ p185 ∨ p41 ∨ p124 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p923 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u12 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u13 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u14 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u15 : p90 := by
    exact h26586
  rcases h20618 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u13)
  · exact False.elim (q1 u15)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u14)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u9)
  · exact False.elim (q9 u0)

theorem step28156 (p8 p13 p161 p710 p897 p904 p1055 p1061 p1229 p1232 p1452 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26899 : p904 ∨ p897)
    (h26927 : p1232 ∨ p1229)
    (h26889 : p710 ∨ p8)
    (h20222 : (¬ p13) ∨ (¬ p161) ∨ (¬ p710) ∨ (¬ p904) ∨ (¬ p1061) ∨ (¬ p1232) ∨ (¬ p1452)) : p1055 ∨ (¬ p13) ∨ p897 ∨ p1229 ∨ (¬ p1452) ∨ p8 ∨ (¬ p161) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1055) := fun hu => hn (Or.inl hu)
  have u1 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20222 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u4)

theorem step28157 (p15 p39 p69 p88 p303 p351 p382 p387 p815 p897 p904 p1096 : Prop)
    (h26899 : p904 ∨ p897)
    (h26867 : p387 ∨ p303)
    (h26833 : p69 ∨ p15)
    (h19140 : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p351) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p815) ∨ (¬ p904) ∨ (¬ p1096)) : (¬ p1096) ∨ p897 ∨ (¬ p815) ∨ (¬ p88) ∨ (¬ p351) ∨ p303 ∨ (¬ p382) ∨ (¬ p39) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p815 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h19140 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u0)

theorem step28159 (p15 p39 p69 p88 p185 p664 p897 p904 p1096 p1115 : Prop)
    (h26899 : p904 ∨ p897)
    (h26833 : p69 ∨ p15)
    (h19308 : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p185) ∨ (¬ p664) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1115)) : (¬ p1115) ∨ p897 ∨ p15 ∨ (¬ p39) ∨ (¬ p185) ∨ (¬ p88) ∨ (¬ p1096) ∨ (¬ p664) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19308 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u0)

theorem step28160 (p15 p69 p224 p657 p897 p904 p1096 : Prop)
    (h26899 : p904 ∨ p897)
    (h26887 : p657 ∨ p224)
    (h26833 : p69 ∨ p15)
    (h20483 : (¬ p69) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1096)) : (¬ p1096) ∨ p897 ∨ p224 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20483 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step28161 (p63 p85 p382 p406 p576 p656 p897 p904 p1325 p1333 p1454 p1644 : Prop)
    (h26899 : p904 ∨ p897)
    (h26835 : p85 ∨ p63)
    (h26869 : p406 ∨ p382)
    (h26931 : p1333 ∨ p1325)
    (h18008 : (¬ p85) ∨ (¬ p406) ∨ (¬ p576) ∨ (¬ p656) ∨ (¬ p904) ∨ (¬ p1333) ∨ (¬ p1454) ∨ (¬ p1644)) : (¬ p1644) ∨ (¬ p1454) ∨ p897 ∨ p63 ∨ p382 ∨ p1325 ∨ (¬ p656) ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1454 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p656 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18008 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u0)

theorem step28162 (p185 p237 p238 p923 p1098 : Prop)
    (h26851 : p237 ∨ p185)
    (h13345 : (¬ p237) ∨ (¬ p238) ∨ (¬ p923) ∨ (¬ p1098)) : (¬ p238) ∨ (¬ p923) ∨ (¬ p1098) ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p923 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1098 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h13345 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)

theorem step28163 (p1055 p1061 p1074 p1098 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h9840 : (¬ p1061) ∨ (¬ p1074) ∨ (¬ p1098)) : (¬ p1098) ∨ (¬ p1074) ∨ p1055 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1098 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h9840 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)

theorem step28172 (p8 p41 p45 p189 p193 p225 p238 p544 p710 : Prop)
    (h26845 : p193 ∨ p189)
    (h26831 : p45 ∨ p41)
    (h26877 : p544 ∨ p225)
    (h26889 : p710 ∨ p8)
    (h19441 : (¬ p45) ∨ (¬ p193) ∨ (¬ p238) ∨ (¬ p544) ∨ (¬ p710)) : (¬ p238) ∨ p189 ∨ p41 ∨ p225 ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19441 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)

theorem step28174 (p8 p15 p16 p18 p19 p101 p102 p238 p710 p836 p840 p1115 : Prop)
    (h26889 : p710 ∨ p8)
    (h26837 : p102 ∨ p101)
    (h26895 : p840 ∨ p836)
    (h26829 : p19 ∨ p18)
    (h19055 : (¬ p15) ∨ (¬ p16) ∨ (¬ p19) ∨ (¬ p102) ∨ (¬ p238) ∨ (¬ p710) ∨ (¬ p840) ∨ (¬ p1115)) : (¬ p1115) ∨ (¬ p15) ∨ p8 ∨ p101 ∨ p836 ∨ p18 ∨ (¬ p16) ∨ (¬ p238) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19055 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u0)

theorem step28175 (p8 p17 p135 p170 p238 p256 p710 p836 p840 : Prop)
    (h26853 : p256 ∨ p17)
    (h26889 : p710 ∨ p8)
    (h26895 : p840 ∨ p836)
    (h20040 : (¬ p135) ∨ (¬ p170) ∨ (¬ p238) ∨ (¬ p256) ∨ (¬ p710) ∨ (¬ p840)) : (¬ p238) ∨ p17 ∨ p8 ∨ (¬ p135) ∨ (¬ p170) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20040 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)

theorem step28179 (p156 p189 p193 p238 p1055 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h26845 : p193 ∨ p189)
    (h16610 : (¬ p156) ∨ (¬ p193) ∨ (¬ p238) ∨ (¬ p1055) ∨ (¬ p1116)) : (¬ p1055) ∨ p1115 ∨ (¬ p238) ∨ p189 ∨ (¬ p156) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1115) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16610 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step28180 (p8 p156 p189 p193 p238 p710 p836 p840 : Prop)
    (h26889 : p710 ∨ p8)
    (h26845 : p193 ∨ p189)
    (h26895 : p840 ∨ p836)
    (h19431 : (¬ p156) ∨ (¬ p193) ∨ (¬ p238) ∨ (¬ p710) ∨ (¬ p840)) : p8 ∨ p189 ∨ (¬ p156) ∨ (¬ p238) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p8) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19431 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)

theorem step28181 (p8 p88 p101 p102 p121 p227 p238 p421 p577 p710 p836 p840 p1115 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26895 : p840 ∨ p836)
    (h26837 : p102 ∨ p101)
    (h26889 : p710 ∨ p8)
    (h19048 : (¬ p88) ∨ (¬ p102) ∨ (¬ p227) ∨ (¬ p238) ∨ (¬ p421) ∨ (¬ p577) ∨ (¬ p710) ∨ (¬ p840) ∨ (¬ p1115) ∨ (¬ p1206)) : p121 ∨ (¬ p1115) ∨ (¬ p577) ∨ (¬ p88) ∨ p836 ∨ (¬ p238) ∨ p101 ∨ (¬ p227) ∨ p8 ∨ (¬ p421) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u11 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u12 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u13 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h19048 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u12)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u13)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u1)
  · exact False.elim (q9 u10)

theorem step28183 (p8 p15 p24 p39 p69 p88 p101 p102 p238 p290 p495 p499 p710 p836 p840 : Prop)
    (h26833 : p69 ∨ p15)
    (h26895 : p840 ∨ p836)
    (h26875 : p499 ∨ p495)
    (h26837 : p102 ∨ p101)
    (h26889 : p710 ∨ p8)
    (h19042 : (¬ p24) ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p102) ∨ (¬ p238) ∨ (¬ p290) ∨ (¬ p499) ∨ (¬ p710) ∨ (¬ p840)) : (¬ p290) ∨ p15 ∨ (¬ p24) ∨ (¬ p238) ∨ p836 ∨ (¬ p88) ∨ p495 ∨ (¬ p39) ∨ p101 ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p290 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u12 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u13 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u14 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h19042 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u13)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u12)
  · exact False.elim (q8 u14)
  · exact False.elim (q9 u11)

theorem step28184 (p6 p10 p127 p190 p238 p323 p347 p836 p1055 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h26861 : p323 ∨ p10)
    (h26839 : p127 ∨ p6)
    (h19035 : (¬ p127) ∨ (¬ p190) ∨ (¬ p238) ∨ (¬ p323) ∨ (¬ p347) ∨ (¬ p836) ∨ (¬ p1055) ∨ (¬ p1116)) : p1115 ∨ (¬ p836) ∨ (¬ p238) ∨ p10 ∨ (¬ p190) ∨ (¬ p1055) ∨ p6 ∨ (¬ p347) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1115) := fun hu => hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19035 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u8)

theorem step28185 (p6 p8 p127 p190 p238 p710 p789 p833 p858 p1325 p1449 p1665 : Prop)
    (h26839 : p127 ∨ p6)
    (h26897 : p858 ∨ p789)
    (h26889 : p710 ∨ p8)
    (h19045 : (¬ p127) ∨ (¬ p190) ∨ (¬ p238) ∨ (¬ p710) ∨ (¬ p833) ∨ (¬ p858) ∨ (¬ p1325) ∨ (¬ p1449) ∨ (¬ p1665)) : (¬ p1665) ∨ p6 ∨ p789 ∨ (¬ p238) ∨ p8 ∨ (¬ p1449) ∨ (¬ p833) ∨ (¬ p1325) ∨ (¬ p190) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p833 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19045 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u0)

theorem step28187 (p17 p238 p256 p836 p1055 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h26853 : p256 ∨ p17)
    (h20170 : (¬ p238) ∨ (¬ p256) ∨ (¬ p836) ∨ (¬ p1055) ∨ (¬ p1116)) : (¬ p836) ∨ p1115 ∨ (¬ p1055) ∨ p17 ∨ (¬ p238) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1115) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20170 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step28188 (p170 p238 p790 p1055 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h25820 : (¬ p790) ∨ (¬ p1116) ∨ (¬ p170) ∨ (¬ p1055) ∨ (¬ p238)) : (¬ p1055) ∨ (¬ p238) ∨ (¬ p790) ∨ p1115 ∨ (¬ p170) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1055 := by
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
  have u3 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25820 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step28189 (p17 p135 p170 p238 p256 p1055 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h26853 : p256 ∨ p17)
    (h19340 : (¬ p135) ∨ (¬ p170) ∨ (¬ p238) ∨ (¬ p256) ∨ (¬ p1055) ∨ (¬ p1116)) : (¬ p238) ∨ (¬ p1055) ∨ p1115 ∨ (¬ p135) ∨ p17 ∨ (¬ p170) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19340 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)

theorem step28190 (p87 p238 p918 p928 p1055 p1115 p1116 : Prop)
    (h26901 : p928 ∨ p918)
    (h26915 : p1116 ∨ p1115)
    (h17534 : (¬ p87) ∨ (¬ p238) ∨ (¬ p928) ∨ (¬ p1055) ∨ (¬ p1116)) : p918 ∨ (¬ p1055) ∨ (¬ p238) ∨ p1115 ∨ (¬ p87) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p918) := fun hu => hn (Or.inl hu)
  have u1 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17534 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)

theorem step28191 (p6 p8 p39 p68 p88 p121 p127 p238 p710 p836 p840 p1081 p1115 : Prop)
    (h26889 : p710 ∨ p8)
    (h26895 : p840 ∨ p836)
    (h26839 : p127 ∨ p6)
    (h19051 : (¬ p39) ∨ (¬ p68) ∨ (¬ p88) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p238) ∨ (¬ p710) ∨ (¬ p840) ∨ (¬ p1081) ∨ (¬ p1115)) : (¬ p1115) ∨ (¬ p68) ∨ p8 ∨ p836 ∨ (¬ p121) ∨ (¬ p1081) ∨ p6 ∨ (¬ p238) ∨ (¬ p88) ∨ (¬ p39) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u12 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19051 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u12)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u0)

theorem step28193 (p923 p1095 p1115 p1116 : Prop)
    (h26914 : (¬ p1115) ∨ (¬ p1116))
    (h11949 : (¬ p923) ∨ (¬ p1095) ∨ p1116) : (¬ p1095) ∨ (¬ p1115) ∨ (¬ p923) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p923 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1116) := by
    rcases h26914 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h11949 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (u3 q2)

theorem step28196 (p3 p41 p45 p90 p110 p185 p192 p226 p237 p923 p1076 p1095 : Prop)
    (h26847 : p226 ∨ p3)
    (h26586 : p90)
    (h26831 : p45 ∨ p41)
    (h26851 : p237 ∨ p185)
    (h17165 : (¬ p45) ∨ (¬ p90) ∨ (¬ p110) ∨ (¬ p192) ∨ (¬ p226) ∨ (¬ p237) ∨ (¬ p923) ∨ (¬ p1076) ∨ (¬ p1095)) : p3 ∨ (¬ p923) ∨ p41 ∨ (¬ p110) ∨ p185 ∨ (¬ p192) ∨ (¬ p1076) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p923 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p192 := by
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
  have u8 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p90 := by
    exact h26586
  have u10 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17165 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step28206 (p633 p636 p641 p648 p649 p650 p651 p652 : Prop)
    (h26884 : (¬ p633) ∨ (¬ p636))
    (h3654 : p636 ∨ p641 ∨ (¬ p648) ∨ (¬ p649) ∨ (¬ p650) ∨ (¬ p651) ∨ (¬ p652)) : p641 ∨ (¬ p649) ∨ (¬ p633) ∨ (¬ p648) ∨ (¬ p652) ∨ (¬ p650) ∨ (¬ p651) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p641) := fun hu => hn (Or.inl hu)
  have u1 : p649 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p648 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p652 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p650 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p651 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p636) := by
    rcases h26884 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h3654 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u4)

theorem step28220 (p639 p1074 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h12040 : (¬ p639) ∨ (¬ p1074) ∨ (¬ p1077)) : p1076 ∨ (¬ p639) ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : p639 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h12040 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step28221 (p344 p639 p980 p1074 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h17846 : (¬ p344) ∨ (¬ p639) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1333)) : (¬ p344) ∨ p1325 ∨ (¬ p1074) ∨ (¬ p639) ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p639 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17846 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step28226 (p124 p304 p494 p639 p1096 : Prop)
    (h26859 : p304 ∨ p124)
    (h9346 : (¬ p304) ∨ (¬ p494) ∨ (¬ p639) ∨ (¬ p1096)) : p124 ∨ (¬ p494) ∨ (¬ p639) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p639 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9346 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)

theorem step28227 (p41 p124 p189 p224 p304 p639 p860 p897 p1346 : Prop)
    (h26859 : p304 ∨ p124)
    (h20086 : (¬ p41) ∨ (¬ p189) ∨ (¬ p224) ∨ (¬ p304) ∨ (¬ p639) ∨ (¬ p860) ∨ (¬ p897) ∨ (¬ p1346)) : (¬ p41) ∨ p124 ∨ (¬ p860) ∨ (¬ p897) ∨ (¬ p1346) ∨ (¬ p224) ∨ (¬ p189) ∨ (¬ p639) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p860 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p639 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20086 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step28228 (p15 p39 p69 p88 p344 p639 p789 p790 p814 p858 p1096 p1325 : Prop)
    (h26833 : p69 ∨ p15)
    (h26893 : p814 ∨ p790)
    (h26897 : p858 ∨ p789)
    (h19311 : (¬ p39) ∨ (¬ p69) ∨ (¬ p88) ∨ (¬ p344) ∨ (¬ p639) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1096) ∨ (¬ p1325)) : (¬ p344) ∨ p15 ∨ (¬ p639) ∨ (¬ p1096) ∨ (¬ p88) ∨ (¬ p1325) ∨ p790 ∨ (¬ p39) ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p639 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h19311 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u3)
  · exact False.elim (q8 u5)

theorem step28229 (p10 p124 p125 p304 p362 p639 p640 : Prop)
    (h26859 : p304 ∨ p124)
    (h26865 : p362 ∨ p125)
    (h25822 : (¬ p10) ∨ (¬ p304) ∨ (¬ p639) ∨ (¬ p362) ∨ (¬ p640)) : (¬ p10) ∨ p124 ∨ (¬ p640) ∨ p125 ∨ (¬ p639) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p640 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p639 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25822 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)

theorem step28232 (p134 p142 p422 p1212 p1256 : Prop)
    (h26928 : (¬ p422) ∨ (¬ p1256))
    (h26841 : p142 ∨ p134)
    (h13679 : (¬ p142) ∨ (¬ p1212) ∨ p1256) : (¬ p422) ∨ (¬ p1212) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1212 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1256) := by
    rcases h26928 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u4 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h13679 with q0 | q1 | q2
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (u3 q2)

theorem step28234 (p3 p11 p126 p301 p1140 p1159 p1208 p1443 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26935 : p1443 ∨ p11)
    (h26857 : p301 ∨ p126)
    (h20506 : (¬ p3) ∨ (¬ p301) ∨ (¬ p1159) ∨ (¬ p1208) ∨ (¬ p1443)) : (¬ p1208) ∨ (¬ p3) ∨ p1140 ∨ p11 ∨ p126 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1208 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p126) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p301 := by
    rcases h26857 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20506 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u6)

theorem step28235 (p642 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h19562 : p642 ∨ (¬ p1077)) : p642 ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p642) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr hu)
  have u2 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19562 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)

theorem step28236 (p17 p185 p237 p286 p576 p581 p1076 p1077 : Prop)
    (h26879 : p581 ∨ p576)
    (h26851 : p237 ∨ p185)
    (h26911 : p1077 ∨ p1076)
    (h17482 : (¬ p17) ∨ (¬ p237) ∨ (¬ p286) ∨ (¬ p581) ∨ (¬ p1077)) : p576 ∨ p185 ∨ p1076 ∨ (¬ p17) ∨ (¬ p286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p286 := by
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
  have u7 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17482 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)

theorem step28238 (p6 p101 p102 p127 p980 p983 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26903 : p983 ∨ p980)
    (h26839 : p127 ∨ p6)
    (h26837 : p102 ∨ p101)
    (h17653 : (¬ p102) ∨ (¬ p127) ∨ (¬ p983) ∨ (¬ p1077)) : p1076 ∨ p980 ∨ p6 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p127 := by
    rcases h26839 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17653 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step28239 (p185 p189 p193 p1076 p1077 p1115 : Prop)
    (h26845 : p193 ∨ p189)
    (h26911 : p1077 ∨ p1076)
    (h17236 : (¬ p185) ∨ (¬ p193) ∨ (¬ p1077) ∨ (¬ p1115)) : (¬ p185) ∨ (¬ p1115) ∨ p189 ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17236 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)

theorem step28240 (p17 p256 p258 p288 p980 p983 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26853 : p256 ∨ p17)
    (h26855 : p288 ∨ p258)
    (h26903 : p983 ∨ p980)
    (h17012 : (¬ p256) ∨ (¬ p288) ∨ (¬ p983) ∨ (¬ p1077)) : p1076 ∨ p17 ∨ p258 ∨ p980 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17012 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)

theorem step28241 (p101 p102 p134 p142 p189 p193 p1076 p1077 : Prop)
    (h26845 : p193 ∨ p189)
    (h26911 : p1077 ∨ p1076)
    (h26841 : p142 ∨ p134)
    (h26837 : p102 ∨ p101)
    (h17269 : (¬ p102) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p1077)) : p189 ∨ p1076 ∨ p134 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p189) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17269 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step28242 (p124 p125 p126 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h19565 : (¬ p124) ∨ (¬ p125) ∨ (¬ p126) ∨ (¬ p1077)) : (¬ p125) ∨ (¬ p124) ∨ p1076 ∨ (¬ p126) := by
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
  have u2 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19565 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step28243 (p101 p102 p209 p305 p1055 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26837 : p102 ∨ p101)
    (h19957 : (¬ p102) ∨ (¬ p209) ∨ (¬ p305) ∨ (¬ p1055) ∨ (¬ p1077)) : p1076 ∨ (¬ p305) ∨ (¬ p209) ∨ (¬ p1055) ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19957 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step28244 (p185 p344 p346 p1076 p1077 p1115 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26863 : p346 ∨ p344)
    (h19080 : (¬ p185) ∨ (¬ p346) ∨ (¬ p1077) ∨ (¬ p1115)) : (¬ p1115) ∨ p1076 ∨ p344 ∨ (¬ p185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19080 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step28245 (p12 p124 p125 p1036 p1076 p1077 : Prop)
    (h26907 : p1036 ∨ p12)
    (h26911 : p1077 ∨ p1076)
    (h17740 : (¬ p124) ∨ (¬ p125) ∨ (¬ p1036) ∨ (¬ p1077)) : p12 ∨ p1076 ∨ (¬ p124) ∨ (¬ p125) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p12) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p125 := by
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
  rcases h17740 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step28249 (p1 p12 p664 p734 p1036 p1366 : Prop)
    (h26907 : p1036 ∨ p12)
    (h16376 : (¬ p1) ∨ (¬ p664) ∨ (¬ p734) ∨ (¬ p1036) ∨ (¬ p1366)) : (¬ p1366) ∨ (¬ p1) ∨ (¬ p734) ∨ p12 ∨ (¬ p664) := by
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
  have u2 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16376 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step28250 (p224 p285 p303 p349 p387 p897 p926 : Prop)
    (h26867 : p387 ∨ p303)
    (h18914 : (¬ p224) ∨ (¬ p285) ∨ (¬ p349) ∨ (¬ p387) ∨ (¬ p897) ∨ (¬ p926)) : p303 ∨ (¬ p897) ∨ (¬ p926) ∨ (¬ p285) ∨ (¬ p224) ∨ (¬ p349) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p285 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h18914 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)

theorem step28251 (p926 p1074 p1115 p1116 : Prop)
    (h26915 : p1116 ∨ p1115)
    (h13519 : (¬ p926) ∨ (¬ p1074) ∨ (¬ p1116)) : (¬ p926) ∨ (¬ p1074) ∨ p1115 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h13519 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step28252 (p836 p840 p897 p926 : Prop)
    (h26895 : p840 ∨ p836)
    (h10259 : (¬ p840) ∨ (¬ p897) ∨ (¬ p926)) : (¬ p926) ∨ (¬ p897) ∨ p836 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h10259 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)

theorem step28254 (p63 p85 p289 p576 p926 p1096 : Prop)
    (h26835 : p85 ∨ p63)
    (h16619 : (¬ p85) ∨ (¬ p289) ∨ (¬ p576) ∨ (¬ p926) ∨ (¬ p1096)) : (¬ p289) ∨ (¬ p1096) ∨ (¬ p576) ∨ p63 ∨ (¬ p926) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p289 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16619 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)

theorem step28267 (p135 p187 p561 p576 p581 p922 p1055 p1061 p1074 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26879 : p581 ∨ p576)
    (h19161 : (¬ p135) ∨ (¬ p187) ∨ (¬ p561) ∨ (¬ p581) ∨ (¬ p922) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p922) ∨ p1055 ∨ (¬ p135) ∨ (¬ p187) ∨ (¬ p1074) ∨ (¬ p561) ∨ p576 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p922 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19161 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u4)

theorem step28268 (p90 p185 p237 p836 p840 p897 p922 : Prop)
    (h26851 : p237 ∨ p185)
    (h26895 : p840 ∨ p836)
    (h26586 : p90)
    (h19352 : (¬ p90) ∨ (¬ p237) ∨ (¬ p840) ∨ (¬ p897) ∨ (¬ p922)) : p185 ∨ (¬ p897) ∨ p836 ∨ (¬ p922) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p185) := fun hu => hn (Or.inl hu)
  have u1 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p922 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p90 := by
    exact h26586
  rcases h19352 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)

theorem step28270 (p63 p85 p922 p1096 : Prop)
    (h26835 : p85 ∨ p63)
    (h8759 : (¬ p85) ∨ (¬ p922) ∨ (¬ p1096)) : (¬ p1096) ∨ p63 ∨ (¬ p922) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p922 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h8759 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)

theorem step28272 (p17 p83 p255 p344 p346 p576 p581 p918 : Prop)
    (h26879 : p581 ∨ p576)
    (h26863 : p346 ∨ p344)
    (h17067 : (¬ p17) ∨ (¬ p83) ∨ (¬ p255) ∨ (¬ p346) ∨ (¬ p581) ∨ (¬ p918)) : (¬ p255) ∨ p576 ∨ (¬ p17) ∨ (¬ p918) ∨ (¬ p83) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p581 := by
    rcases h26879 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17067 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)

theorem step28280 (p258 p288 p434 p514 p1015 : Prop)
    (h26855 : p288 ∨ p258)
    (h24176 : (¬ p514) ∨ (¬ p1015) ∨ (¬ p288) ∨ (¬ p434)) : (¬ p514) ∨ (¬ p1015) ∨ (¬ p434) ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p514 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h24176 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step28281 (p258 p288 p303 p387 p514 p789 p858 : Prop)
    (h26867 : p387 ∨ p303)
    (h26855 : p288 ∨ p258)
    (h26897 : p858 ∨ p789)
    (h24177 : (¬ p514) ∨ (¬ p387) ∨ (¬ p288) ∨ (¬ p858)) : (¬ p514) ∨ p303 ∨ p258 ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p514 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h24177 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)

theorem step28282 (p258 p288 p364 p382 p406 p514 p789 p858 : Prop)
    (h26869 : p406 ∨ p382)
    (h26855 : p288 ∨ p258)
    (h26897 : p858 ∨ p789)
    (h24178 : (¬ p364) ∨ (¬ p514) ∨ (¬ p288) ∨ (¬ p406) ∨ (¬ p858)) : (¬ p514) ∨ p382 ∨ (¬ p364) ∨ p258 ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p514 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p382) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h24178 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)

theorem step28283 (p303 p387 p438 p790 p1022 : Prop)
    (h26867 : p387 ∨ p303)
    (h17223 : (¬ p387) ∨ (¬ p438) ∨ (¬ p790) ∨ (¬ p1022)) : (¬ p1022) ∨ p303 ∨ (¬ p790) ∨ (¬ p438) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17223 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)

theorem step28285 (p2 p156 p185 p192 p303 p387 p419 p517 p790 : Prop)
    (h26867 : p387 ∨ p303)
    (h20028 : (¬ p2) ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p192) ∨ (¬ p387) ∨ (¬ p419) ∨ (¬ p517) ∨ (¬ p790)) : (¬ p517) ∨ (¬ p2) ∨ p303 ∨ (¬ p185) ∨ (¬ p419) ∨ (¬ p192) ∨ (¬ p790) ∨ (¬ p156) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p517 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20028 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u6)

theorem step28297 (p258 p285 p288 p296 p297 p298 p299 p300 : Prop)
    (h26854 : (¬ p258) ∨ (¬ p288))
    (h1493 : p285 ∨ p288 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : (¬ p300) ∨ (¬ p298) ∨ (¬ p258) ∨ (¬ p297) ∨ (¬ p296) ∨ (¬ p299) ∨ p285 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p300 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p298 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p297 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p296 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p299 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p285) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p288) := by
    rcases h26854 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h1493 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u0)

theorem step28299 (p125 p265 p286 p576 p918 p928 : Prop)
    (h26901 : p928 ∨ p918)
    (h24179 : (¬ p125) ∨ (¬ p576) ∨ (¬ p265) ∨ (¬ p286) ∨ (¬ p928)) : (¬ p576) ∨ (¬ p125) ∨ p918 ∨ (¬ p265) ∨ (¬ p286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h24179 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step28307 (p17 p41 p45 p303 p420 p579 p1022 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h26831 : p45 ∨ p41)
    (h25828 : (¬ p1393) ∨ (¬ p45) ∨ (¬ p303) ∨ (¬ p420) ∨ (¬ p17) ∨ (¬ p1022) ∨ (¬ p579)) : (¬ p579) ∨ (¬ p420) ∨ (¬ p17) ∨ (¬ p303) ∨ p1385 ∨ p41 ∨ (¬ p1022) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u8 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h25828 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u0)

theorem step28308 (p17 p83 p420 p438 p579 p980 p983 p1055 p1061 p1335 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26903 : p983 ∨ p980)
    (h22722 : (¬ p17) ∨ (¬ p438) ∨ (¬ p83) ∨ (¬ p420) ∨ (¬ p579) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1335)) : (¬ p420) ∨ p1055 ∨ (¬ p579) ∨ (¬ p1335) ∨ p980 ∨ (¬ p17) ∨ (¬ p438) ∨ (¬ p83) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h22722 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u3)

theorem step28309 (p125 p362 p420 p421 : Prop)
    (h26865 : p362 ∨ p125)
    (h11290 : (¬ p362) ∨ (¬ p420) ∨ (¬ p421)) : (¬ p420) ∨ (¬ p421) ∨ p125 := by
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
  have u3 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h11290 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)

theorem step28310 (p125 p362 p420 p455 p1452 : Prop)
    (h26865 : p362 ∨ p125)
    (h18242 : (¬ p362) ∨ (¬ p420) ∨ (¬ p455) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p420) ∨ p125 ∨ (¬ p455) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18242 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)

theorem step28311 (p125 p362 p420 p455 p498 p980 p983 p1056 p1081 p1103 p1226 : Prop)
    (h26903 : p983 ∨ p980)
    (h26865 : p362 ∨ p125)
    (h19380 : (¬ p362) ∨ (¬ p420) ∨ (¬ p455) ∨ (¬ p498) ∨ (¬ p983) ∨ (¬ p1056) ∨ (¬ p1081) ∨ (¬ p1103) ∨ (¬ p1226)) : (¬ p420) ∨ (¬ p498) ∨ (¬ p455) ∨ (¬ p1226) ∨ (¬ p1056) ∨ p980 ∨ (¬ p1103) ∨ (¬ p1081) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p455 := by
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
  have u5 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h19380 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u3)

theorem step28313 (p125 p241 p362 p420 p455 p918 p980 p983 p1056 p1081 p1226 : Prop)
    (h26903 : p983 ∨ p980)
    (h26865 : p362 ∨ p125)
    (h20348 : (¬ p241) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p455) ∨ (¬ p918) ∨ (¬ p983) ∨ (¬ p1056) ∨ (¬ p1081) ∨ (¬ p1226)) : (¬ p420) ∨ (¬ p1081) ∨ (¬ p241) ∨ (¬ p1226) ∨ (¬ p1056) ∨ p980 ∨ p125 ∨ (¬ p455) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
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
  have u5 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20348 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u3)

theorem step28314 (p3 p12 p41 p45 p125 p192 p226 p362 p420 p455 p498 p1036 p1081 : Prop)
    (h26847 : p226 ∨ p3)
    (h26907 : p1036 ∨ p12)
    (h26865 : p362 ∨ p125)
    (h26831 : p45 ∨ p41)
    (h19451 : (¬ p45) ∨ (¬ p192) ∨ (¬ p226) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p455) ∨ (¬ p498) ∨ (¬ p1036) ∨ (¬ p1081)) : p3 ∨ (¬ p192) ∨ p12 ∨ (¬ p1081) ∨ (¬ p455) ∨ p125 ∨ p41 ∨ (¬ p420) ∨ (¬ p498) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u12 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19451 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u12)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u3)

theorem step28315 (p86 p189 p193 p303 p420 p422 p495 p1000 p1256 : Prop)
    (h26929 : p1256 ∨ p422)
    (h26845 : p193 ∨ p189)
    (h16954 : (¬ p86) ∨ (¬ p193) ∨ (¬ p303) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p1000) ∨ (¬ p1256)) : (¬ p420) ∨ p422 ∨ (¬ p495) ∨ (¬ p303) ∨ (¬ p86) ∨ p189 ∨ (¬ p1000) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p422) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
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
    · exact False.elim (u5 q1)
  rcases h16954 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step28316 (p349 p420 p633 p636 : Prop)
    (h26884 : (¬ p633) ∨ (¬ p636))
    (h12598 : (¬ p349) ∨ (¬ p420) ∨ p636) : (¬ p420) ∨ (¬ p349) ∨ (¬ p633) := by
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
  have u3 : (¬ p636) := by
    rcases h26884 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h12598 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (u3 q2)

theorem step28317 (p124 p303 p304 p420 p633 : Prop)
    (h26859 : p304 ∨ p124)
    (h18842 : (¬ p303) ∨ (¬ p304) ∨ (¬ p420) ∨ (¬ p633)) : (¬ p420) ∨ p124 ∨ (¬ p303) ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18842 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)

theorem step28318 (p3 p6 p14 p17 p23 p126 p229 p256 p420 : Prop)
    (h26853 : p256 ∨ p17)
    (h26849 : p229 ∨ p14)
    (h19379 : (¬ p3) ∨ (¬ p6) ∨ (¬ p23) ∨ (¬ p126) ∨ (¬ p229) ∨ (¬ p256) ∨ (¬ p420)) : (¬ p420) ∨ p17 ∨ (¬ p126) ∨ p14 ∨ (¬ p23) ∨ (¬ p3) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19379 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u0)

theorem step28319 (p101 p102 p121 p420 p455 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26837 : p102 ∨ p101)
    (h24180 : (¬ p455) ∨ (¬ p1206) ∨ (¬ p102) ∨ (¬ p420)) : p121 ∨ (¬ p420) ∨ (¬ p455) ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h24180 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)

theorem step28320 (p327 p382 p406 p419 p420 p455 p494 p617 p961 : Prop)
    (h26869 : p406 ∨ p382)
    (h16233 : (¬ p327) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p420) ∨ (¬ p455) ∨ (¬ p494) ∨ (¬ p617) ∨ (¬ p961)) : p382 ∨ (¬ p420) ∨ (¬ p617) ∨ (¬ p961) ∨ (¬ p419) ∨ (¬ p327) ∨ (¬ p494) ∨ (¬ p455) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16233 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u3)

theorem step28323 (p4 p290 p420 p633 p836 p840 : Prop)
    (h26895 : p840 ∨ p836)
    (h19636 : (¬ p4) ∨ (¬ p290) ∨ (¬ p420) ∨ (¬ p633) ∨ (¬ p840)) : (¬ p420) ∨ (¬ p4) ∨ p836 ∨ (¬ p633) ∨ (¬ p290) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p290 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19636 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step28325 (p121 p125 p362 p420 p961 : Prop)
    (h26865 : p362 ∨ p125)
    (h19934 : (¬ p121) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p961)) : (¬ p420) ∨ (¬ p121) ∨ p125 ∨ (¬ p961) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19934 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)

theorem step28326 (p41 p124 p189 p304 p420 p494 p517 p633 p790 : Prop)
    (h26859 : p304 ∨ p124)
    (h20084 : (¬ p41) ∨ (¬ p189) ∨ (¬ p304) ∨ (¬ p420) ∨ (¬ p494) ∨ (¬ p517) ∨ (¬ p633) ∨ (¬ p790)) : (¬ p517) ∨ (¬ p420) ∨ p124 ∨ (¬ p494) ∨ (¬ p41) ∨ (¬ p189) ∨ (¬ p633) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p517 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p189 := by
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
  have u8 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20084 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)

theorem step28328 (p17 p256 p420 p515 p583 p601 p790 p814 : Prop)
    (h26893 : p814 ∨ p790)
    (h26853 : p256 ∨ p17)
    (h26881 : p601 ∨ p420)
    (h17176 : (¬ p256) ∨ (¬ p515) ∨ (¬ p583) ∨ (¬ p601) ∨ (¬ p814)) : (¬ p515) ∨ p790 ∨ (¬ p583) ∨ p17 ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p515 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p790) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p583 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17176 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u5)

theorem step28335 (p420 p597 p601 p609 p610 p611 p612 p613 : Prop)
    (h26880 : (¬ p420) ∨ (¬ p601))
    (h3397 : p597 ∨ p601 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : (¬ p613) ∨ p597 ∨ (¬ p420) ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p613 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p597) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p609 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p610 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p611 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p612 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p601) := by
    rcases h26880 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h3397 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u0)

theorem step28340 (p303 p515 p789 p858 : Prop)
    (h26896 : (¬ p789) ∨ (¬ p858))
    (h13579 : (¬ p303) ∨ (¬ p515) ∨ p858) : (¬ p515) ∨ (¬ p789) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p515 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p858) := by
    rcases h26896 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h13579 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (u3 q2)

theorem step28341 (p789 p858 p861 : Prop)
    (h26896 : (¬ p789) ∨ (¬ p858))
    (h21400 : p861 ∨ p858) : p861 ∨ (¬ p789) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p861) := fun hu => hn (Or.inl hu)
  have u1 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p858) := by
    rcases h26896 with q0 | q1
    · exact False.elim (q0 u1)
    · exact q1
  rcases h21400 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)

theorem step28349 (p789 p858 p864 p865 p866 p867 p868 p869 : Prop)
    (h26896 : (¬ p789) ∨ (¬ p858))
    (h4941 : p858 ∨ p864 ∨ (¬ p865) ∨ (¬ p866) ∨ (¬ p867) ∨ (¬ p868) ∨ (¬ p869)) : (¬ p869) ∨ (¬ p868) ∨ (¬ p789) ∨ p864 ∨ (¬ p866) ∨ (¬ p865) ∨ (¬ p867) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p869 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p868 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p864) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p866 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p865 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p867 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p858) := by
    rcases h26896 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h4941 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u0)

theorem step28362 (p41 p45 p189 p193 p801 p1366 p1385 p1393 : Prop)
    (h26845 : p193 ∨ p189)
    (h26831 : p45 ∨ p41)
    (h26933 : p1393 ∨ p1385)
    (h17784 : (¬ p45) ∨ (¬ p193) ∨ (¬ p801) ∨ (¬ p1366) ∨ (¬ p1393)) : p189 ∨ p41 ∨ (¬ p801) ∨ p1385 ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p189) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p41) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p801 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17784 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)

theorem step28364 (p12 p103 p143 p258 p288 p1036 p1076 p1077 : Prop)
    (h26907 : p1036 ∨ p12)
    (h26855 : p288 ∨ p258)
    (h26911 : p1077 ∨ p1076)
    (h16281 : (¬ p103) ∨ (¬ p143) ∨ (¬ p288) ∨ (¬ p1036) ∨ (¬ p1077)) : (¬ p103) ∨ p12 ∨ p258 ∨ (¬ p143) ∨ p1076 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16281 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)

theorem step28365 (p10 p103 p225 p323 p348 : Prop)
    (h26861 : p323 ∨ p10)
    (h12924 : (¬ p103) ∨ (¬ p225) ∨ (¬ p323) ∨ (¬ p348)) : (¬ p103) ∨ (¬ p348) ∨ (¬ p225) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h12924 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)

theorem step28368 (p2 p8 p18 p72 p103 p348 p431 p438 p481 p560 p710 p789 p1189 p1391 : Prop)
    (h26889 : p710 ∨ p8)
    (h26873 : p481 ∨ p2)
    (h20572 : (¬ p18) ∨ (¬ p72) ∨ (¬ p103) ∨ (¬ p348) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p481) ∨ (¬ p560) ∨ (¬ p710) ∨ (¬ p789) ∨ (¬ p1189) ∨ (¬ p1391)) : (¬ p1189) ∨ (¬ p103) ∨ (¬ p72) ∨ (¬ p789) ∨ (¬ p438) ∨ (¬ p1391) ∨ p8 ∨ p2 ∨ (¬ p431) ∨ (¬ p348) ∨ (¬ p18) ∨ (¬ p560) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p72 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1391 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))
  have u12 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u13 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20572 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u13)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u12)
  · exact False.elim (q9 u3)
  · exact False.elim (q10 u0)
  · exact False.elim (q11 u5)

theorem step28380 (p124 p304 p350 p438 p687 : Prop)
    (h26859 : p304 ∨ p124)
    (h22082 : (¬ p687) ∨ (¬ p438) ∨ (¬ p304) ∨ (¬ p350)) : p124 ∨ (¬ p687) ∨ (¬ p350) ∨ (¬ p438) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h22082 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step28385 (p344 p346 p455 p456 p640 p897 p904 p1080 : Prop)
    (h26871 : p456 ∨ p455)
    (h26899 : p904 ∨ p897)
    (h26863 : p346 ∨ p344)
    (h18878 : (¬ p346) ∨ (¬ p456) ∨ (¬ p640) ∨ (¬ p904) ∨ (¬ p1080)) : p455 ∨ p897 ∨ (¬ p640) ∨ p344 ∨ (¬ p1080) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p640 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18878 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)

theorem step28386 (p303 p364 p382 p406 : Prop)
    (h26869 : p406 ∨ p382)
    (h2332 : (¬ p303) ∨ (¬ p364) ∨ (¬ p406)) : p382 ∨ (¬ p364) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2332 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step28387 (p126 p224 p258 p364 p382 p406 : Prop)
    (h26869 : p406 ∨ p382)
    (h20139 : (¬ p126) ∨ (¬ p224) ∨ (¬ p258) ∨ (¬ p364) ∨ (¬ p406)) : p382 ∨ (¬ p258) ∨ (¬ p364) ∨ (¬ p224) ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p382) := fun hu => hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h20139 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step28388 (p124 p126 p224 p264 p304 p344 p346 p364 p687 : Prop)
    (h26859 : p304 ∨ p124)
    (h26863 : p346 ∨ p344)
    (h25830 : (¬ p304) ∨ (¬ p364) ∨ (¬ p126) ∨ (¬ p687) ∨ (¬ p264) ∨ (¬ p224) ∨ (¬ p346)) : (¬ p364) ∨ p124 ∨ (¬ p224) ∨ (¬ p126) ∨ (¬ p687) ∨ p344 ∨ (¬ p264) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p264 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h25830 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u8)

theorem step28389 (p10 p101 p224 p323 p364 p382 p406 : Prop)
    (h26869 : p406 ∨ p382)
    (h26861 : p323 ∨ p10)
    (h19740 : (¬ p101) ∨ (¬ p224) ∨ (¬ p323) ∨ (¬ p364) ∨ (¬ p406)) : (¬ p364) ∨ (¬ p101) ∨ (¬ p224) ∨ p382 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19740 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step28390 (p134 p142 p364 p420 p424 p480 p601 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26841 : p142 ∨ p134)
    (h26881 : p601 ∨ p420)
    (h25831 : (¬ p364) ∨ (¬ p796) ∨ (¬ p601) ∨ (¬ p142) ∨ (¬ p480)) : p424 ∨ (¬ p364) ∨ (¬ p480) ∨ p134 ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p480 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25831 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)

theorem step28391 (p462 p495 p499 p1229 : Prop)
    (h26875 : p499 ∨ p495)
    (h13692 : (¬ p462) ∨ (¬ p499) ∨ p1229) : (¬ p462) ∨ p1229 ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p462 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h13692 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)

theorem step28401 (p303 p434 p595 p616 p1545 : Prop)
    (h26883 : p616 ∨ p595)
    (h16997 : (¬ p303) ∨ (¬ p434) ∨ (¬ p616) ∨ (¬ p1545)) : (¬ p434) ∨ (¬ p1545) ∨ (¬ p303) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16997 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)

theorem step28402 (p419 p595 p616 p1195 p1229 : Prop)
    (h26883 : p616 ∨ p595)
    (h20808 : (¬ p1229) ∨ (¬ p419) ∨ (¬ p616) ∨ (¬ p1195)) : (¬ p1195) ∨ (¬ p1229) ∨ p595 ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20808 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step28403 (p63 p224 p595 p616 p657 p789 p858 p1388 : Prop)
    (h26883 : p616 ∨ p595)
    (h26887 : p657 ∨ p224)
    (h26897 : p858 ∨ p789)
    (h19026 : (¬ p63) ∨ (¬ p616) ∨ (¬ p657) ∨ (¬ p858) ∨ (¬ p1388)) : p595 ∨ p224 ∨ (¬ p63) ∨ p789 ∨ (¬ p1388) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p595) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1388 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19026 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u4)

theorem step28404 (p595 p616 p789 p1015 p1287 : Prop)
    (h26883 : p616 ∨ p595)
    (h16601 : (¬ p616) ∨ (¬ p789) ∨ (¬ p1015) ∨ (¬ p1287)) : (¬ p1015) ∨ (¬ p789) ∨ p595 ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16601 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)

theorem step28405 (p63 p258 p519 p595 p616 p789 p1287 : Prop)
    (h26883 : p616 ∨ p595)
    (h19280 : (¬ p63) ∨ (¬ p258) ∨ (¬ p519) ∨ (¬ p616) ∨ (¬ p789) ∨ (¬ p1287)) : (¬ p789) ∨ (¬ p258) ∨ (¬ p1287) ∨ p595 ∨ (¬ p519) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p519 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19280 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u2)

theorem step28407 (p495 p595 p600 p616 : Prop)
    (h26883 : p616 ∨ p595)
    (h10283 : p495 ∨ (¬ p600) ∨ (¬ p616)) : p495 ∨ p595 ∨ (¬ p600) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p600 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h10283 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step28409 (p17 p86 p126 p256 p434 p595 p616 p1287 : Prop)
    (h26853 : p256 ∨ p17)
    (h26883 : p616 ∨ p595)
    (h25832 : (¬ p1287) ∨ (¬ p126) ∨ (¬ p256) ∨ (¬ p86) ∨ (¬ p616) ∨ (¬ p434)) : (¬ p434) ∨ p17 ∨ (¬ p126) ∨ (¬ p1287) ∨ (¬ p86) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h25832 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u0)

theorem step28410 (p258 p519 p595 p616 p1022 p1545 : Prop)
    (h26883 : p616 ∨ p595)
    (h20228 : (¬ p258) ∨ (¬ p519) ∨ (¬ p616) ∨ (¬ p1022) ∨ (¬ p1545)) : (¬ p1022) ∨ (¬ p258) ∨ (¬ p1545) ∨ (¬ p519) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p519 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20228 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u2)

theorem step28411 (p15 p595 p616 p1287 p1325 : Prop)
    (h26883 : p616 ∨ p595)
    (h16477 : (¬ p15) ∨ (¬ p616) ∨ (¬ p1287) ∨ (¬ p1325)) : p595 ∨ (¬ p15) ∨ (¬ p1287) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p595) := fun hu => hn (Or.inl hu)
  have u1 : p15 := by
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
  have u4 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16477 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)

theorem step28412 (p63 p595 p616 p1287 p1325 : Prop)
    (h26883 : p616 ∨ p595)
    (h17802 : (¬ p63) ∨ (¬ p616) ∨ (¬ p1287) ∨ (¬ p1325)) : p595 ∨ (¬ p1287) ∨ (¬ p1325) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p595) := fun hu => hn (Or.inl hu)
  have u1 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17802 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)

theorem step28413 (p17 p86 p126 p256 p303 p387 p431 p595 p616 p1545 : Prop)
    (h26867 : p387 ∨ p303)
    (h26883 : p616 ∨ p595)
    (h26853 : p256 ∨ p17)
    (h18055 : (¬ p86) ∨ (¬ p126) ∨ (¬ p256) ∨ (¬ p387) ∨ (¬ p431) ∨ (¬ p616) ∨ (¬ p1545)) : p303 ∨ (¬ p431) ∨ (¬ p86) ∨ p595 ∨ (¬ p1545) ∨ (¬ p126) ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18055 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u4)

theorem step28414 (p15 p419 p595 p616 p996 p1287 : Prop)
    (h26905 : p996 ∨ p419)
    (h26883 : p616 ∨ p595)
    (h16430 : (¬ p15) ∨ (¬ p616) ∨ (¬ p996) ∨ (¬ p1287)) : p419 ∨ (¬ p15) ∨ (¬ p1287) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p419) := fun hu => hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16430 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)

theorem step28415 (p18 p19 p39 p63 p121 p228 p595 p616 p1287 : Prop)
    (h26829 : p19 ∨ p18)
    (h26883 : p616 ∨ p595)
    (h17603 : (¬ p19) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p121) ∨ (¬ p228) ∨ (¬ p616) ∨ (¬ p1287)) : p18 ∨ p595 ∨ (¬ p63) ∨ (¬ p1287) ∨ (¬ p121) ∨ (¬ p39) ∨ (¬ p228) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p18) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17603 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u3)

theorem step28416 (p595 p616 p897 p904 p1096 p1287 : Prop)
    (h26899 : p904 ∨ p897)
    (h26883 : p616 ∨ p595)
    (h16630 : (¬ p616) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1287)) : (¬ p1096) ∨ p897 ∨ p595 ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16630 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)

theorem step28417 (p15 p161 p595 p616 p1288 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26883 : p616 ∨ p595)
    (h16499 : (¬ p15) ∨ (¬ p161) ∨ (¬ p616) ∨ (¬ p1288) ∨ (¬ p1333)) : p1325 ∨ p595 ∨ (¬ p161) ∨ (¬ p15) ∨ (¬ p1288) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16499 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step28420 (p15 p22 p420 p434 p595 p601 p616 p1287 : Prop)
    (h26883 : p616 ∨ p595)
    (h26881 : p601 ∨ p420)
    (h25833 : (¬ p1287) ∨ (¬ p616) ∨ (¬ p434) ∨ (¬ p15) ∨ (¬ p22) ∨ (¬ p601)) : (¬ p434) ∨ p595 ∨ (¬ p22) ∨ (¬ p15) ∨ (¬ p1287) ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p22 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h25833 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)

theorem step28422 (p15 p22 p124 p126 p258 p421 p595 p603 p616 : Prop)
    (h26883 : p616 ∨ p595)
    (h19507 : (¬ p15) ∨ (¬ p22) ∨ (¬ p124) ∨ (¬ p126) ∨ (¬ p258) ∨ (¬ p421) ∨ (¬ p603) ∨ (¬ p616)) : (¬ p421) ∨ p595 ∨ (¬ p22) ∨ (¬ p258) ∨ (¬ p15) ∨ (¬ p603) ∨ (¬ p126) ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p22 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p603 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19507 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u8)

theorem step28423 (p89 p595 p616 p790 p1388 : Prop)
    (h26883 : p616 ∨ p595)
    (h12538 : (¬ p89) ∨ (¬ p616) ∨ (¬ p790) ∨ (¬ p1388)) : (¬ p1388) ∨ (¬ p790) ∨ p595 ∨ (¬ p89) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1388 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h12538 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)

theorem step28424 (p15 p49 p84 p185 p237 p595 p616 p665 p1115 p1116 p1287 : Prop)
    (h26851 : p237 ∨ p185)
    (h26915 : p1116 ∨ p1115)
    (h26883 : p616 ∨ p595)
    (h20145 : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p237) ∨ (¬ p616) ∨ (¬ p665) ∨ (¬ p1116) ∨ (¬ p1287)) : (¬ p84) ∨ p185 ∨ p1115 ∨ p595 ∨ (¬ p1287) ∨ (¬ p49) ∨ (¬ p15) ∨ (¬ p665) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20145 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u4)

theorem step28425 (p595 p616 p1229 p1232 p1288 : Prop)
    (h26926 : (¬ p1229) ∨ (¬ p1232))
    (h26883 : p616 ∨ p595)
    (h10250 : (¬ p616) ∨ p1232 ∨ (¬ p1288)) : (¬ p1229) ∨ p595 ∨ (¬ p1288) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1232) := by
    rcases h26926 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u4 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h10250 with q0 | q1 | q2
  · exact False.elim (q0 u4)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u2)

theorem step28426 (p63 p161 p595 p616 p1288 p1325 p1333 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26883 : p616 ∨ p595)
    (h18463 : (¬ p63) ∨ (¬ p161) ∨ (¬ p616) ∨ (¬ p1288) ∨ (¬ p1333)) : p1325 ∨ p595 ∨ (¬ p161) ∨ (¬ p63) ∨ (¬ p1288) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1325) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18463 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step28427 (p101 p121 p124 p211 p228 p595 p616 p1287 : Prop)
    (h26883 : p616 ∨ p595)
    (h25834 : (¬ p1287) ∨ (¬ p616) ∨ (¬ p101) ∨ (¬ p228) ∨ (¬ p211) ∨ (¬ p121) ∨ (¬ p124)) : (¬ p211) ∨ (¬ p101) ∨ p595 ∨ (¬ p228) ∨ (¬ p124) ∨ (¬ p121) ∨ (¬ p1287) := by
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
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25834 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u4)

theorem step28429 (p8 p39 p63 p68 p561 p595 p616 p728 p789 p858 p1388 : Prop)
    (h26883 : p616 ∨ p595)
    (h26897 : p858 ∨ p789)
    (h25835 : (¬ p858) ∨ (¬ p63) ∨ (¬ p728) ∨ (¬ p616) ∨ (¬ p1388) ∨ (¬ p68) ∨ (¬ p8) ∨ (¬ p561) ∨ (¬ p39)) : p595 ∨ (¬ p561) ∨ (¬ p1388) ∨ (¬ p63) ∨ p789 ∨ (¬ p68) ∨ (¬ p728) ∨ (¬ p8) ∨ (¬ p39) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p595) := fun hu => hn (Or.inl hu)
  have u1 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1388 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25835 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u8)

theorem step28430 (p39 p63 p68 p561 p595 p616 p980 p983 p1015 p1055 p1061 p1335 p1388 : Prop)
    (h26903 : p983 ∨ p980)
    (h26909 : p1061 ∨ p1055)
    (h26883 : p616 ∨ p595)
    (h19211 : (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p561) ∨ (¬ p616) ∨ (¬ p983) ∨ (¬ p1015) ∨ (¬ p1061) ∨ (¬ p1335) ∨ (¬ p1388)) : p980 ∨ p1055 ∨ p595 ∨ (¬ p1388) ∨ (¬ p561) ∨ (¬ p39) ∨ (¬ p68) ∨ (¬ p1015) ∨ (¬ p1335) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1388 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p68 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u11 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u12 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19211 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u12)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u8)
  · exact False.elim (q9 u3)

theorem step28431 (p12 p88 p163 p167 p189 p595 p616 p1036 p1229 p1309 p1389 : Prop)
    (h26843 : p167 ∨ p163)
    (h26883 : p616 ∨ p595)
    (h26907 : p1036 ∨ p12)
    (h19009 : (¬ p88) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p616) ∨ (¬ p1036) ∨ (¬ p1229) ∨ (¬ p1309) ∨ (¬ p1389)) : (¬ p1389) ∨ (¬ p1229) ∨ (¬ p1309) ∨ p163 ∨ (¬ p88) ∨ (¬ p189) ∨ p595 ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19009 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u0)

theorem step28432 (p2 p3 p14 p226 p303 p327 p387 p481 p595 p616 p1287 : Prop)
    (h26867 : p387 ∨ p303)
    (h26847 : p226 ∨ p3)
    (h26873 : p481 ∨ p2)
    (h26883 : p616 ∨ p595)
    (h19258 : (¬ p14) ∨ (¬ p226) ∨ (¬ p327) ∨ (¬ p387) ∨ (¬ p481) ∨ (¬ p616) ∨ (¬ p1287)) : p303 ∨ p3 ∨ (¬ p327) ∨ p2 ∨ (¬ p14) ∨ (¬ p1287) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19258 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u5)

theorem step28433 (p3 p12 p595 p616 p980 p983 p1335 p1545 : Prop)
    (h26883 : p616 ∨ p595)
    (h26903 : p983 ∨ p980)
    (h25836 : (¬ p616) ∨ (¬ p1545) ∨ (¬ p983) ∨ (¬ p12) ∨ (¬ p3) ∨ (¬ p1335)) : (¬ p12) ∨ (¬ p3) ∨ (¬ p1545) ∨ p595 ∨ p980 ∨ (¬ p1335) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25836 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u5)

theorem step28434 (p3 p225 p303 p351 p387 p544 p595 p616 p1287 : Prop)
    (h26867 : p387 ∨ p303)
    (h26877 : p544 ∨ p225)
    (h26883 : p616 ∨ p595)
    (h25837 : (¬ p387) ∨ (¬ p1287) ∨ (¬ p544) ∨ (¬ p351) ∨ (¬ p3) ∨ (¬ p616)) : p303 ∨ (¬ p3) ∨ p225 ∨ (¬ p1287) ∨ p595 ∨ (¬ p351) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25837 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u8)

theorem step28435 (p2 p84 p163 p186 p424 p481 p595 p616 p796 p929 p1096 p1545 : Prop)
    (h26891 : p796 ∨ p424)
    (h26873 : p481 ∨ p2)
    (h26883 : p616 ∨ p595)
    (h16974 : (¬ p84) ∨ (¬ p163) ∨ (¬ p186) ∨ (¬ p481) ∨ (¬ p616) ∨ (¬ p796) ∨ (¬ p929) ∨ (¬ p1096) ∨ (¬ p1545)) : p424 ∨ (¬ p1096) ∨ (¬ p1545) ∨ (¬ p186) ∨ p2 ∨ (¬ p163) ∨ (¬ p929) ∨ (¬ p84) ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p163 := by
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
  have u8 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h16974 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u2)

theorem step28436 (p303 p387 p495 p499 p595 p616 p1287 : Prop)
    (h26867 : p387 ∨ p303)
    (h26875 : p499 ∨ p495)
    (h26883 : p616 ∨ p595)
    (h18703 : (¬ p387) ∨ (¬ p499) ∨ (¬ p616) ∨ (¬ p1287)) : p303 ∨ p495 ∨ p595 ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
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
  have u6 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18703 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)

theorem step28437 (p434 p495 p499 p595 p616 p1545 : Prop)
    (h26875 : p499 ∨ p495)
    (h26883 : p616 ∨ p595)
    (h19210 : (¬ p434) ∨ (¬ p499) ∨ (¬ p616) ∨ (¬ p1545)) : (¬ p434) ∨ (¬ p1545) ∨ p495 ∨ p595 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19210 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)

theorem step28438 (p12 p88 p124 p163 p167 p189 p498 p595 p616 p633 p636 p1036 p1389 : Prop)
    (h26885 : p636 ∨ p633)
    (h26883 : p616 ∨ p595)
    (h26907 : p1036 ∨ p12)
    (h26843 : p167 ∨ p163)
    (h19962 : (¬ p88) ∨ (¬ p124) ∨ (¬ p167) ∨ (¬ p189) ∨ (¬ p498) ∨ (¬ p616) ∨ (¬ p636) ∨ (¬ p1036) ∨ (¬ p1389)) : (¬ p1389) ∨ p633 ∨ p595 ∨ (¬ p189) ∨ p12 ∨ (¬ p124) ∨ p163 ∨ (¬ p498) ∨ (¬ p88) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p633) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u12 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19962 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u12)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u0)

theorem step28442 (p1096 p1099 p1103 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h17390 : (¬ p1099) ∨ p1103) : p1096 ∨ p1103 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1096) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1103) := fun hu => hn (Or.inr hu)
  have u2 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17390 with q0 | q1
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)

theorem step28444 (p303 p595 p1096 p1099 p1286 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h19953 : (¬ p303) ∨ (¬ p595) ∨ (¬ p1099) ∨ (¬ p1286)) : (¬ p1286) ∨ (¬ p595) ∨ (¬ p303) ∨ p1096 := by
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
  have u2 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19953 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step28445 (p224 p897 p1096 p1099 p1325 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h16958 : (¬ p224) ∨ (¬ p897) ∨ (¬ p1099) ∨ (¬ p1325)) : p1096 ∨ (¬ p897) ∨ (¬ p224) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1096) := fun hu => hn (Or.inl hu)
  have u1 : p897 := by
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
  have u4 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16958 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)

theorem step28447 (p224 p728 p898 p1096 p1099 p1545 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h16914 : (¬ p224) ∨ (¬ p728) ∨ (¬ p898) ∨ (¬ p1099) ∨ (¬ p1545)) : (¬ p728) ∨ (¬ p224) ∨ (¬ p1545) ∨ p1096 ∨ (¬ p898) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p898 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16914 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)

theorem step28449 (p39 p63 p68 p101 p102 p121 p211 p227 p642 p1096 p1099 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26913 : p1099 ∨ p1096)
    (h26837 : p102 ∨ p101)
    (h17621 : (¬ p39) ∨ (¬ p63) ∨ (¬ p68) ∨ (¬ p102) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p642) ∨ (¬ p1099) ∨ (¬ p1206)) : p121 ∨ (¬ p227) ∨ (¬ p68) ∨ (¬ p211) ∨ (¬ p63) ∨ (¬ p39) ∨ (¬ p642) ∨ p1096 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p642 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h17621 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u9)

theorem step28450 (p344 p897 p1076 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h17054 : (¬ p344) ∨ (¬ p897) ∨ (¬ p1076) ∨ (¬ p1099)) : (¬ p344) ∨ (¬ p1076) ∨ p1096 ∨ (¬ p897) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17054 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step28451 (p20 p495 p499 p534 p1096 p1099 p1538 : Prop)
    (h26875 : p499 ∨ p495)
    (h26913 : p1099 ∨ p1096)
    (h16505 : (¬ p20) ∨ (¬ p499) ∨ (¬ p534) ∨ (¬ p1099) ∨ (¬ p1538)) : (¬ p1538) ∨ (¬ p534) ∨ p495 ∨ (¬ p20) ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p20 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16505 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)

theorem step28452 (p344 p346 p595 p642 p902 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26863 : p346 ∨ p344)
    (h16456 : (¬ p346) ∨ (¬ p595) ∨ (¬ p642) ∨ (¬ p902) ∨ (¬ p1099)) : p1096 ∨ p344 ∨ (¬ p642) ∨ (¬ p595) ∨ (¬ p902) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p902 := by
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
  rcases h16456 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step28454 (p12 p63 p108 p1074 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h19936 : (¬ p12) ∨ (¬ p63) ∨ (¬ p108) ∨ (¬ p1074) ∨ (¬ p1099)) : (¬ p12) ∨ p1096 ∨ (¬ p1074) ∨ (¬ p108) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19936 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step28455 (p11 p17 p86 p256 p985 p1096 p1099 p1443 p1452 p1538 : Prop)
    (h26853 : p256 ∨ p17)
    (h26913 : p1099 ∨ p1096)
    (h26935 : p1443 ∨ p11)
    (h18855 : (¬ p86) ∨ (¬ p256) ∨ (¬ p985) ∨ (¬ p1099) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p1538)) : (¬ p1538) ∨ (¬ p1452) ∨ p17 ∨ p1096 ∨ (¬ p86) ∨ p11 ∨ (¬ p985) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p985 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18855 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u0)

theorem step28456 (p86 p789 p790 p985 p1096 p1099 p1325 p1333 p1538 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h26913 : p1099 ∨ p1096)
    (h20151 : (¬ p86) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p985) ∨ (¬ p1099) ∨ (¬ p1333) ∨ (¬ p1538)) : (¬ p1538) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p985) ∨ p1325 ∨ (¬ p86) ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1538 := by
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
  have u4 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u8 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20151 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u0)

theorem step28457 (p63 p85 p927 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26834 : (¬ p63) ∨ (¬ p85))
    (h12049 : p85 ∨ (¬ p927) ∨ (¬ p1099)) : (¬ p927) ∨ p1096 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u4 : (¬ p85) := by
    rcases h26834 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h12049 with q0 | q1 | q2
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)

theorem step28458 (p15 p18 p19 p105 p880 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26829 : p19 ∨ p18)
    (h16326 : (¬ p15) ∨ (¬ p19) ∨ (¬ p105) ∨ (¬ p880) ∨ (¬ p1099)) : (¬ p880) ∨ p1096 ∨ (¬ p15) ∨ p18 ∨ (¬ p105) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16326 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step28459 (p15 p884 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h8753 : (¬ p15) ∨ (¬ p884) ∨ (¬ p1099)) : p1096 ∨ (¬ p884) ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1096) := fun hu => hn (Or.inl hu)
  have u1 : p884 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8753 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step28460 (p12 p15 p1074 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h16331 : (¬ p12) ∨ (¬ p15) ∨ (¬ p1074) ∨ (¬ p1099)) : p1096 ∨ (¬ p12) ∨ (¬ p15) ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1096) := fun hu => hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16331 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step28462 (p344 p633 p897 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h17061 : (¬ p344) ∨ (¬ p633) ∨ (¬ p897) ∨ (¬ p1099)) : (¬ p344) ∨ (¬ p897) ∨ p1096 ∨ (¬ p633) := by
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
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17061 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step28463 (p38 p71 p884 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h8755 : (¬ p38) ∨ (¬ p71) ∨ (¬ p884) ∨ (¬ p1099)) : p1096 ∨ (¬ p884) ∨ (¬ p71) ∨ (¬ p38) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1096) := fun hu => hn (Or.inl hu)
  have u1 : p884 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8755 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step28464 (p15 p17 p49 p84 p126 p256 p347 p897 p1096 p1099 : Prop)
    (h26853 : p256 ∨ p17)
    (h26913 : p1099 ∨ p1096)
    (h17363 : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p126) ∨ (¬ p256) ∨ (¬ p347) ∨ (¬ p897) ∨ (¬ p1099)) : (¬ p347) ∨ (¬ p84) ∨ (¬ p15) ∨ (¬ p126) ∨ (¬ p897) ∨ p17 ∨ p1096 ∨ (¬ p49) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u9 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17363 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u9)

theorem step28465 (p86 p189 p193 p224 p422 p897 p1000 p1096 p1099 p1256 : Prop)
    (h26929 : p1256 ∨ p422)
    (h26845 : p193 ∨ p189)
    (h26913 : p1099 ∨ p1096)
    (h18790 : (¬ p86) ∨ (¬ p193) ∨ (¬ p224) ∨ (¬ p897) ∨ (¬ p1000) ∨ (¬ p1099) ∨ (¬ p1256)) : p422 ∨ p189 ∨ (¬ p224) ∨ (¬ p1000) ∨ (¬ p86) ∨ (¬ p897) ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p422) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18790 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u7)

theorem step28466 (p734 p897 p1035 p1096 p1099 p1140 p1335 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h25838 : (¬ p1035) ∨ (¬ p734) ∨ (¬ p1335) ∨ (¬ p1140) ∨ (¬ p897) ∨ (¬ p1099)) : (¬ p1035) ∨ (¬ p1140) ∨ (¬ p897) ∨ (¬ p734) ∨ (¬ p1335) ∨ p1096 := by
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
  have u2 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h25838 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)

theorem step28468 (p15 p980 p1074 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h16339 : (¬ p15) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1099)) : p1096 ∨ (¬ p1074) ∨ (¬ p980) ∨ (¬ p15) := by
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
  have u3 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16339 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step28469 (p15 p49 p84 p185 p237 p668 p897 p1096 p1099 p1115 p1116 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26851 : p237 ∨ p185)
    (h26915 : p1116 ∨ p1115)
    (h20309 : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p237) ∨ (¬ p668) ∨ (¬ p897) ∨ (¬ p1099) ∨ (¬ p1116)) : (¬ p84) ∨ p1096 ∨ (¬ p15) ∨ (¬ p668) ∨ p185 ∨ p1115 ∨ (¬ p49) ∨ (¬ p897) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20309 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u10)

theorem step28470 (p495 p499 p640 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26875 : p499 ∨ p495)
    (h8731 : (¬ p499) ∨ (¬ p640) ∨ (¬ p1099)) : p1096 ∨ (¬ p640) ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1096) := fun hu => hn (Or.inl hu)
  have u1 : p640 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h8731 with q0 | q1 | q2
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step28471 (p344 p495 p499 p897 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26875 : p499 ∨ p495)
    (h16514 : (¬ p344) ∨ (¬ p499) ∨ (¬ p897) ∨ (¬ p1099)) : p1096 ∨ (¬ p897) ∨ (¬ p344) ∨ p495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1096) := fun hu => hn (Or.inl hu)
  have u1 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16514 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step28472 (p125 p348 p362 p496 p897 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26865 : p362 ∨ p125)
    (h18824 : (¬ p348) ∨ (¬ p362) ∨ (¬ p496) ∨ (¬ p897) ∨ (¬ p1099)) : (¬ p348) ∨ p1096 ∨ (¬ p897) ∨ p125 ∨ (¬ p496) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18824 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step28474 (p41 p63 p156 p923 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h18407 : (¬ p41) ∨ (¬ p63) ∨ (¬ p156) ∨ (¬ p923) ∨ (¬ p1099)) : (¬ p41) ∨ p1096 ∨ (¬ p63) ∨ (¬ p923) ∨ (¬ p156) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p923 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p156 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18407 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step28475 (p125 p362 p434 p496 p980 p1074 p1096 p1099 p1330 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26865 : p362 ∨ p125)
    (h18036 : (¬ p362) ∨ (¬ p434) ∨ (¬ p496) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1330)) : (¬ p434) ∨ p1096 ∨ (¬ p1074) ∨ (¬ p1330) ∨ (¬ p496) ∨ (¬ p980) ∨ p125 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18036 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step28476 (p6 p18 p19 p48 p192 p799 p1385 : Prop)
    (h26829 : p19 ∨ p18)
    (h17370 : (¬ p6) ∨ (¬ p19) ∨ (¬ p48) ∨ (¬ p192) ∨ (¬ p799) ∨ (¬ p1385)) : (¬ p1385) ∨ (¬ p192) ∨ (¬ p799) ∨ (¬ p6) ∨ (¬ p48) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p799 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17370 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u0)

theorem step28477 (p18 p19 p48 p134 p790 p1385 : Prop)
    (h26829 : p19 ∨ p18)
    (h20383 : (¬ p19) ∨ (¬ p48) ∨ (¬ p134) ∨ (¬ p790) ∨ (¬ p1385)) : (¬ p790) ∨ (¬ p1385) ∨ (¬ p48) ∨ (¬ p134) ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p19 := by
    rcases h26829 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20383 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step28478 (p48 p124 p304 p344 p346 p424 p425 p542 p582 p1711 p1712 : Prop)
    (h26859 : p304 ∨ p124)
    (h26863 : p346 ∨ p344)
    (h18841 : (¬ p48) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p424) ∨ (¬ p425) ∨ (¬ p542) ∨ (¬ p582) ∨ (¬ p1711) ∨ (¬ p1712)) : (¬ p1712) ∨ (¬ p1711) ∨ (¬ p542) ∨ p124 ∨ p344 ∨ (¬ p425) ∨ (¬ p424) ∨ (¬ p582) ∨ (¬ p48) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1712 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1711 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18841 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u0)

theorem step28481 (p2 p48 p68 p134 p142 p344 p346 p424 p481 p495 p499 p582 p635 p796 p1096 p1099 : Prop)
    (h26891 : p796 ∨ p424)
    (h26863 : p346 ∨ p344)
    (h26875 : p499 ∨ p495)
    (h26873 : p481 ∨ p2)
    (h26841 : p142 ∨ p134)
    (h26913 : p1099 ∨ p1096)
    (h20287 : (¬ p48) ∨ (¬ p68) ∨ (¬ p142) ∨ (¬ p346) ∨ (¬ p481) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p635) ∨ (¬ p796) ∨ (¬ p1099)) : p424 ∨ p344 ∨ p495 ∨ p2 ∨ (¬ p582) ∨ p134 ∨ (¬ p635) ∨ (¬ p48) ∨ p1096 ∨ (¬ p68) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p635 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u11 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u12 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u13 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u14 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u15 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h20287 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u14)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u13)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u15)

theorem step28482 (p3 p48 p68 p125 p163 p167 p303 p422 p425 p582 p1000 p1256 : Prop)
    (h26843 : p167 ∨ p163)
    (h26929 : p1256 ∨ p422)
    (h17290 : (¬ p3) ∨ (¬ p48) ∨ (¬ p68) ∨ (¬ p125) ∨ (¬ p167) ∨ (¬ p303) ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p1000) ∨ (¬ p1256)) : (¬ p425) ∨ p163 ∨ (¬ p582) ∨ (¬ p125) ∨ (¬ p303) ∨ (¬ p1000) ∨ (¬ p48) ∨ (¬ p3) ∨ (¬ p68) ∨ p422 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p422) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p1256 := by
    rcases h26929 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h17290 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u5)
  · exact False.elim (q9 u11)

theorem step28484 (p14 p48 p87 p163 p167 p189 : Prop)
    (h26843 : p167 ∨ p163)
    (h19589 : (¬ p14) ∨ (¬ p48) ∨ (¬ p87) ∨ (¬ p167) ∨ (¬ p189)) : (¬ p48) ∨ p163 ∨ (¬ p189) ∨ (¬ p14) ∨ (¬ p87) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h19589 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)

theorem step28485 (p2 p48 p64 p234 p495 p499 p582 : Prop)
    (h26875 : p499 ∨ p495)
    (h18840 : (¬ p2) ∨ (¬ p48) ∨ (¬ p64) ∨ (¬ p234) ∨ (¬ p499) ∨ (¬ p582)) : (¬ p2) ∨ p495 ∨ (¬ p48) ∨ (¬ p64) ∨ (¬ p582) ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h18840 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u4)

theorem step28486 (p15 p48 p63 p69 : Prop)
    (h26833 : p69 ∨ p15)
    (h11773 : (¬ p48) ∨ (¬ p63) ∨ (¬ p69)) : (¬ p48) ∨ p15 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h11773 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step28490 (p3 p14 p17 p64 p86 p226 p234 p256 p258 p288 p325 p1187 : Prop)
    (h26853 : p256 ∨ p17)
    (h26847 : p226 ∨ p3)
    (h26855 : p288 ∨ p258)
    (h26921 : p1187 ∨ p234)
    (h24181 : (¬ p325) ∨ (¬ p1187) ∨ (¬ p86) ∨ (¬ p226) ∨ (¬ p256) ∨ (¬ p64) ∨ (¬ p288) ∨ (¬ p14)) : (¬ p325) ∨ p17 ∨ p3 ∨ (¬ p64) ∨ p258 ∨ (¬ p86) ∨ p234 ∨ (¬ p14) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p234) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h24181 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u10)
  · exact False.elim (q7 u7)

theorem step28492 (p3 p64 p226 p344 p346 p756 p940 : Prop)
    (h26863 : p346 ∨ p344)
    (h26847 : p226 ∨ p3)
    (h17998 : (¬ p64) ∨ (¬ p226) ∨ (¬ p346) ∨ (¬ p756) ∨ (¬ p940)) : (¬ p940) ∨ (¬ p756) ∨ (¬ p64) ∨ p344 ∨ p3 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17998 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step28494 (p64 p124 p206 p304 p455 p456 p633 p790 p814 p1346 p1385 p1393 p1490 : Prop)
    (h26893 : p814 ∨ p790)
    (h26871 : p456 ∨ p455)
    (h26859 : p304 ∨ p124)
    (h26933 : p1393 ∨ p1385)
    (h20557 : (¬ p64) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p456) ∨ (¬ p633) ∨ (¬ p814) ∨ (¬ p1346) ∨ (¬ p1393) ∨ (¬ p1490)) : (¬ p1490) ∨ (¬ p1346) ∨ p790 ∨ (¬ p64) ∨ p455 ∨ (¬ p206) ∨ p124 ∨ p1385 ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1490 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p455) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u12 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h20557 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u12)
  · exact False.elim (q8 u0)

theorem step28495 (p2 p14 p17 p64 p86 p110 p229 p234 p256 p258 p288 : Prop)
    (h26853 : p256 ∨ p17)
    (h26855 : p288 ∨ p258)
    (h26849 : p229 ∨ p14)
    (h17191 : (¬ p2) ∨ (¬ p64) ∨ (¬ p86) ∨ (¬ p110) ∨ (¬ p229) ∨ (¬ p234) ∨ (¬ p256) ∨ (¬ p288)) : (¬ p2) ∨ p17 ∨ (¬ p64) ∨ (¬ p234) ∨ (¬ p110) ∨ p258 ∨ p14 ∨ (¬ p86) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p14) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17191 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u9)

theorem step28496 (p11 p17 p84 p225 p256 p534 p929 p1443 p1452 p1538 : Prop)
    (h26853 : p256 ∨ p17)
    (h26935 : p1443 ∨ p11)
    (h18209 : (¬ p84) ∨ (¬ p225) ∨ (¬ p256) ∨ (¬ p534) ∨ (¬ p929) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p1538)) : (¬ p1538) ∨ (¬ p534) ∨ p17 ∨ (¬ p84) ∨ (¬ p929) ∨ p11 ∨ (¬ p225) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18209 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u0)

theorem step28497 (p14 p15 p63 p85 p106 p929 p1074 p1076 p1077 : Prop)
    (h26835 : p85 ∨ p63)
    (h26911 : p1077 ∨ p1076)
    (h16554 : (¬ p14) ∨ (¬ p15) ∨ (¬ p85) ∨ (¬ p106) ∨ (¬ p929) ∨ (¬ p1074) ∨ (¬ p1077)) : (¬ p15) ∨ p63 ∨ (¬ p106) ∨ (¬ p1074) ∨ (¬ p14) ∨ p1076 ∨ (¬ p929) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1076) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h16554 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u8)

theorem step28498 (p17 p84 p126 p256 p303 p387 p929 p1096 p1229 p1232 p1295 : Prop)
    (h26927 : p1232 ∨ p1229)
    (h26867 : p387 ∨ p303)
    (h26853 : p256 ∨ p17)
    (h16973 : (¬ p84) ∨ (¬ p126) ∨ (¬ p256) ∨ (¬ p387) ∨ (¬ p929) ∨ (¬ p1096) ∨ (¬ p1232) ∨ (¬ p1295)) : (¬ p1295) ∨ p1229 ∨ p303 ∨ p17 ∨ (¬ p929) ∨ (¬ p1096) ∨ (¬ p84) ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1295 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16973 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u0)

theorem step28500 (p50 p424 p435 p796 p1193 p1542 : Prop)
    (h26891 : p796 ∨ p424)
    (h16913 : (¬ p50) ∨ (¬ p435) ∨ (¬ p796) ∨ (¬ p1193) ∨ (¬ p1542)) : (¬ p1542) ∨ p424 ∨ (¬ p435) ∨ (¬ p50) ∨ (¬ p1193) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p424) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p50 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16913 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)

theorem step28505 (p38 p47 p101 p102 p121 p124 p206 p304 p790 p799 p814 p1206 p1346 p1490 : Prop)
    (h26859 : p304 ∨ p124)
    (h26923 : p1206 ∨ p121)
    (h26893 : p814 ∨ p790)
    (h26837 : p102 ∨ p101)
    (h16526 : (¬ p38) ∨ (¬ p47) ∨ (¬ p102) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p799) ∨ (¬ p814) ∨ (¬ p1206) ∨ (¬ p1346) ∨ (¬ p1490)) : (¬ p38) ∨ (¬ p47) ∨ p124 ∨ (¬ p1346) ∨ (¬ p206) ∨ p121 ∨ (¬ p799) ∨ p790 ∨ p101 ∨ (¬ p1490) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p799 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p790) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1490 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u12 : p814 := by
    rcases h26893 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u13 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h16526 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u13)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u12)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u3)
  · exact False.elim (q9 u9)

theorem step28506 (p6 p38 p49 p63 p85 p101 p1076 p1229 p1309 : Prop)
    (h26835 : p85 ∨ p63)
    (h16544 : (¬ p6) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p101) ∨ (¬ p1076) ∨ (¬ p1229) ∨ (¬ p1309)) : (¬ p101) ∨ (¬ p1076) ∨ (¬ p38) ∨ p63 ∨ (¬ p49) ∨ (¬ p1309) ∨ (¬ p1229) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16544 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u5)

theorem step28508 (p38 p49 p63 p85 p101 p102 p121 p124 p206 p304 p460 p1206 p1229 : Prop)
    (h26859 : p304 ∨ p124)
    (h26837 : p102 ∨ p101)
    (h26923 : p1206 ∨ p121)
    (h26835 : p85 ∨ p63)
    (h16674 : (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p102) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p460) ∨ (¬ p1206) ∨ (¬ p1229)) : (¬ p460) ∨ p124 ∨ (¬ p1229) ∨ (¬ p38) ∨ p101 ∨ (¬ p206) ∨ (¬ p49) ∨ p121 ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p460 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u11 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u12 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h16674 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u12)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u2)

theorem step28509 (p10 p38 p101 p102 p124 p206 p304 p517 p615 p687 p1015 p1190 : Prop)
    (h26837 : p102 ∨ p101)
    (h26859 : p304 ∨ p124)
    (h16680 : (¬ p10) ∨ (¬ p38) ∨ (¬ p102) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p517) ∨ (¬ p615) ∨ (¬ p687) ∨ (¬ p1015) ∨ (¬ p1190)) : (¬ p615) ∨ (¬ p1190) ∨ (¬ p687) ∨ (¬ p206) ∨ (¬ p10) ∨ (¬ p517) ∨ (¬ p38) ∨ p101 ∨ (¬ p1015) ∨ p124 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p615 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p206 := by
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
  have u6 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h16680 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u8)
  · exact False.elim (q9 u1)

theorem step28511 (p2 p38 p49 p63 p85 p419 p595 p1542 : Prop)
    (h26835 : p85 ∨ p63)
    (h25839 : (¬ p1542) ∨ (¬ p2) ∨ (¬ p85) ∨ (¬ p38) ∨ (¬ p595) ∨ (¬ p49) ∨ (¬ p419)) : (¬ p1542) ∨ (¬ p2) ∨ (¬ p419) ∨ p63 ∨ (¬ p595) ∨ (¬ p49) ∨ (¬ p38) := by
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
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25839 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u2)

theorem step28512 (p6 p38 p101 p141 p258 p288 : Prop)
    (h26855 : p288 ∨ p258)
    (h25840 : (¬ p101) ∨ (¬ p6) ∨ (¬ p288) ∨ (¬ p141) ∨ (¬ p38)) : (¬ p101) ∨ p258 ∨ (¬ p6) ∨ (¬ p38) ∨ (¬ p141) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p258) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p288 := by
    rcases h26855 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25840 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)

theorem step28513 (p6 p38 p49 p84 p789 p790 p1325 p1333 p1454 p1666 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h20305 : (¬ p6) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1333) ∨ (¬ p1454) ∨ (¬ p1666)) : (¬ p1666) ∨ (¬ p1454) ∨ (¬ p49) ∨ (¬ p84) ∨ p1325 ∨ (¬ p6) ∨ (¬ p790) ∨ (¬ p789) ∨ (¬ p38) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1454 := by
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
  have u4 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20305 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u0)

theorem step28517 (p10 p38 p49 p63 p85 p101 p102 p124 p206 p304 p595 p599 : Prop)
    (h26859 : p304 ∨ p124)
    (h26837 : p102 ∨ p101)
    (h26835 : p85 ∨ p63)
    (h16708 : (¬ p10) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p102) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p595) ∨ (¬ p599)) : (¬ p38) ∨ p124 ∨ p101 ∨ (¬ p206) ∨ (¬ p10) ∨ (¬ p599) ∨ p63 ∨ (¬ p49) ∨ (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p599 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h16708 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u5)

theorem step28518 (p10 p38 p49 p84 p206 p789 p790 p1325 p1333 p1624 p1665 : Prop)
    (h26931 : p1333 ∨ p1325)
    (h20306 : (¬ p10) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p206) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p1333) ∨ (¬ p1624) ∨ (¬ p1665)) : (¬ p1665) ∨ (¬ p1624) ∨ (¬ p38) ∨ (¬ p10) ∨ p1325 ∨ (¬ p789) ∨ (¬ p206) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20306 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u1)
  · exact False.elim (q9 u0)

theorem step28519 (p6 p38 p49 p63 p85 p101 p350 p420 p495 p499 p601 : Prop)
    (h26881 : p601 ∨ p420)
    (h26875 : p499 ∨ p495)
    (h26835 : p85 ∨ p63)
    (h16488 : (¬ p6) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p101) ∨ (¬ p350) ∨ (¬ p499) ∨ (¬ p601)) : (¬ p101) ∨ (¬ p350) ∨ p420 ∨ p495 ∨ (¬ p6) ∨ (¬ p38) ∨ (¬ p49) ∨ p63 := by
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
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h16488 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u8)

theorem step28520 (p6 p38 p49 p121 p532 p1022 p1206 p1330 p1385 p1393 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26933 : p1393 ∨ p1385)
    (h16667 : (¬ p6) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p532) ∨ (¬ p1022) ∨ (¬ p1206) ∨ (¬ p1330) ∨ (¬ p1393)) : (¬ p1022) ∨ p121 ∨ (¬ p532) ∨ p1385 ∨ (¬ p6) ∨ (¬ p49) ∨ (¬ p38) ∨ (¬ p1330) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16667 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u9)

theorem step28521 (p38 p49 p63 p85 p101 p121 p206 p638 p961 p1096 : Prop)
    (h26835 : p85 ∨ p63)
    (h16658 : (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p206) ∨ (¬ p638) ∨ (¬ p961) ∨ (¬ p1096)) : (¬ p101) ∨ (¬ p961) ∨ (¬ p38) ∨ (¬ p638) ∨ p63 ∨ (¬ p121) ∨ (¬ p1096) ∨ (¬ p206) ∨ (¬ p49) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p638 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h16658 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u6)

theorem step28523 (p6 p38 p49 p63 p85 p121 p389 p595 p1206 p1286 : Prop)
    (h26923 : p1206 ∨ p121)
    (h26835 : p85 ∨ p63)
    (h16671 : (¬ p6) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p389) ∨ (¬ p595) ∨ (¬ p1206) ∨ (¬ p1286)) : (¬ p389) ∨ p121 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p1286) ∨ (¬ p595) ∨ (¬ p6) ∨ p63 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h16671 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u4)

theorem step28525 (p3 p38 p163 p226 p261 p423 p532 p961 p1000 p1325 p1333 : Prop)
    (h26847 : p226 ∨ p3)
    (h26931 : p1333 ∨ p1325)
    (h19107 : (¬ p38) ∨ (¬ p163) ∨ (¬ p226) ∨ (¬ p261) ∨ (¬ p423) ∨ (¬ p532) ∨ (¬ p961) ∨ (¬ p1000) ∨ (¬ p1333)) : (¬ p961) ∨ (¬ p423) ∨ (¬ p1000) ∨ p3 ∨ p1325 ∨ (¬ p532) ∨ (¬ p163) ∨ (¬ p261) ∨ (¬ p38) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19107 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u2)
  · exact False.elim (q8 u10)

theorem step28526 (p3 p14 p38 p226 : Prop)
    (h26847 : p226 ∨ p3)
    (h11954 : (¬ p14) ∨ (¬ p38) ∨ (¬ p226)) : p3 ∨ (¬ p14) ∨ (¬ p38) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h11954 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)

theorem step28529 (p6 p38 p43 p134 p142 p424 p595 p796 p924 p1096 p1099 p1191 : Prop)
    (h26891 : p796 ∨ p424)
    (h26841 : p142 ∨ p134)
    (h26913 : p1099 ∨ p1096)
    (h18941 : (¬ p6) ∨ (¬ p38) ∨ (¬ p43) ∨ (¬ p142) ∨ (¬ p595) ∨ (¬ p796) ∨ (¬ p924) ∨ (¬ p1099) ∨ (¬ p1191)) : p424 ∨ p134 ∨ (¬ p38) ∨ (¬ p6) ∨ (¬ p1191) ∨ (¬ p43) ∨ p1096 ∨ (¬ p924) ∨ (¬ p595) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p134) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p924 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18941 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u4)

theorem step28530 (p14 p38 p163 p167 p303 p387 p420 p495 p499 p601 p1004 p1140 p1159 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26867 : p387 ∨ p303)
    (h26843 : p167 ∨ p163)
    (h26875 : p499 ∨ p495)
    (h26881 : p601 ∨ p420)
    (h19400 : (¬ p14) ∨ (¬ p38) ∨ (¬ p167) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1004) ∨ (¬ p1159)) : p1140 ∨ p303 ∨ (¬ p14) ∨ p163 ∨ p495 ∨ (¬ p38) ∨ (¬ p1004) ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1004 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u12 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19400 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u8)

theorem step28531 (p3 p38 p43 p226 p461 p495 p577 p980 p983 p1037 p1081 p1229 p1465 : Prop)
    (h26847 : p226 ∨ p3)
    (h26903 : p983 ∨ p980)
    (h18122 : (¬ p38) ∨ (¬ p43) ∨ (¬ p226) ∨ (¬ p461) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p983) ∨ (¬ p1037) ∨ (¬ p1081) ∨ (¬ p1229) ∨ (¬ p1465)) : (¬ p1037) ∨ (¬ p1229) ∨ p3 ∨ (¬ p38) ∨ (¬ p43) ∨ p980 ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p461) ∨ (¬ p1465) ∨ (¬ p1081) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1037 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p461 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u12 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18122 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u12)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u1)
  · exact False.elim (q10 u9)

theorem step28532 (p38 p43 p134 p161 p495 p577 p1225 p1229 p1713 p1798 : Prop)
    (h26925 : p1225 ∨ p161)
    (h18124 : (¬ p38) ∨ (¬ p43) ∨ (¬ p134) ∨ (¬ p495) ∨ (¬ p577) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1713) ∨ (¬ p1798)) : (¬ p1798) ∨ (¬ p1713) ∨ (¬ p43) ∨ (¬ p495) ∨ p161 ∨ (¬ p577) ∨ (¬ p134) ∨ (¬ p38) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1798 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1713 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p161) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p577 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p1225 := by
    rcases h26925 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18124 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u0)

theorem step28539 (p6 p25 p67 p121 p455 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h17330 : (¬ p6) ∨ (¬ p25) ∨ (¬ p67) ∨ (¬ p455) ∨ (¬ p1206)) : p121 ∨ (¬ p455) ∨ (¬ p6) ∨ (¬ p67) ∨ (¬ p25) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p25 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17330 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)

theorem step28540 (p6 p13 p14 p24 p67 p455 p456 p980 p1035 p1042 : Prop)
    (h26871 : p456 ∨ p455)
    (h17335 : (¬ p6) ∨ (¬ p13) ∨ (¬ p14) ∨ (¬ p24) ∨ (¬ p67) ∨ (¬ p456) ∨ (¬ p980) ∨ (¬ p1035) ∨ (¬ p1042)) : p455 ∨ (¬ p1035) ∨ (¬ p980) ∨ (¬ p67) ∨ (¬ p1042) ∨ (¬ p14) ∨ (¬ p6) ∨ (¬ p13) ∨ (¬ p24) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1042 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17335 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u4)

theorem step28541 (p6 p10 p25 p67 p420 p601 : Prop)
    (h26881 : p601 ∨ p420)
    (h17985 : (¬ p6) ∨ (¬ p10) ∨ (¬ p25) ∨ (¬ p67) ∨ (¬ p601)) : (¬ p10) ∨ (¬ p25) ∨ p420 ∨ (¬ p67) ∨ (¬ p6) := by
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
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17985 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step28543 (p8 p710 p897 p904 p1102 : Prop)
    (h26899 : p904 ∨ p897)
    (h26889 : p710 ∨ p8)
    (h10245 : (¬ p710) ∨ (¬ p904) ∨ (¬ p1102)) : p897 ∨ p8 ∨ (¬ p1102) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p897) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p8) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h10245 with q0 | q1 | q2
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)

theorem step28547 (p63 p85 p126 p224 p347 p382 p495 p499 p579 p657 p709 p929 p1102 : Prop)
    (h26875 : p499 ∨ p495)
    (h26835 : p85 ∨ p63)
    (h26887 : p657 ∨ p224)
    (h16772 : (¬ p85) ∨ (¬ p126) ∨ (¬ p347) ∨ (¬ p382) ∨ (¬ p499) ∨ (¬ p579) ∨ (¬ p657) ∨ (¬ p709) ∨ (¬ p929) ∨ (¬ p1102)) : (¬ p579) ∨ (¬ p347) ∨ p495 ∨ (¬ p382) ∨ (¬ p1102) ∨ p63 ∨ p224 ∨ (¬ p709) ∨ (¬ p929) ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u12 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h16772 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u11)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u12)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u8)
  · exact False.elim (q9 u4)

theorem step28548 (p15 p163 p880 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h25843 : (¬ p1099) ∨ (¬ p880) ∨ (¬ p15) ∨ (¬ p163)) : (¬ p880) ∨ p1096 ∨ (¬ p15) ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h25843 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)

theorem step28549 (p12 p15 p880 p1036 p1076 p1077 p1096 p1099 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26913 : p1099 ∨ p1096)
    (h26907 : p1036 ∨ p12)
    (h16394 : (¬ p15) ∨ (¬ p880) ∨ (¬ p1036) ∨ (¬ p1077) ∨ (¬ p1099)) : p1076 ∨ p1096 ∨ (¬ p880) ∨ p12 ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16394 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step28550 (p306 p382 p406 p419 p543 p680 p726 p727 : Prop)
    (h26869 : p406 ∨ p382)
    (h16206 : (¬ p306) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p543) ∨ (¬ p680) ∨ (¬ p726) ∨ (¬ p727)) : (¬ p727) ∨ (¬ p306) ∨ (¬ p726) ∨ p382 ∨ (¬ p543) ∨ (¬ p680) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p727 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p382) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p543 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p406 := by
    rcases h26869 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16206 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u0)

theorem step28551 (p134 p138 p142 : Prop)
    (h26841 : p142 ∨ p134)
    (h16293 : p138 ∨ (¬ p142)) : p138 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p138) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p134) := fun hu => hn (Or.inr hu)
  have u2 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h16293 with q0 | q1
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)

theorem step28552 (p134 p142 p209 : Prop)
    (h26841 : p142 ∨ p134)
    (h16869 : (¬ p142) ∨ p209) : p134 ∨ p209 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p134) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p209) := fun hu => hn (Or.inr hu)
  have u2 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16869 with q0 | q1
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)

theorem step28553 (p134 p142 p195 : Prop)
    (h26841 : p142 ∨ p134)
    (h17873 : (¬ p142) ∨ p195) : p134 ∨ p195 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p134) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p195) := fun hu => hn (Or.inr hu)
  have u2 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17873 with q0 | q1
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)

theorem step28554 (p6 p134 p142 p192 : Prop)
    (h26841 : p142 ∨ p134)
    (h9328 : (¬ p6) ∨ (¬ p142) ∨ (¬ p192)) : (¬ p192) ∨ p134 ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p134) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h9328 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u0)

theorem step28555 (p121 p134 p142 p189 p193 p243 p980 p983 p1056 p1081 p1226 : Prop)
    (h26903 : p983 ∨ p980)
    (h26845 : p193 ∨ p189)
    (h26841 : p142 ∨ p134)
    (h16724 : (¬ p121) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p243) ∨ (¬ p983) ∨ (¬ p1056) ∨ (¬ p1081) ∨ (¬ p1226)) : p980 ∨ (¬ p1226) ∨ (¬ p1056) ∨ (¬ p121) ∨ (¬ p1081) ∨ p189 ∨ (¬ p243) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p980) := fun hu => hn (Or.inl hu)
  have u1 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1056 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p243 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h16724 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u1)

theorem step28556 (p101 p102 p134 p142 p189 p193 p344 : Prop)
    (h26845 : p193 ∨ p189)
    (h26837 : p102 ∨ p101)
    (h26841 : p142 ∨ p134)
    (h16731 : (¬ p102) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p344)) : (¬ p344) ∨ p189 ∨ p101 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16731 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)

theorem step28557 (p10 p134 p142 p189 p193 p224 p323 p347 p382 p657 p821 : Prop)
    (h26845 : p193 ∨ p189)
    (h26861 : p323 ∨ p10)
    (h26887 : p657 ∨ p224)
    (h26841 : p142 ∨ p134)
    (h16758 : (¬ p142) ∨ (¬ p193) ∨ (¬ p323) ∨ (¬ p347) ∨ (¬ p382) ∨ (¬ p657) ∨ (¬ p821)) : (¬ p347) ∨ p189 ∨ p10 ∨ (¬ p382) ∨ (¬ p821) ∨ p224 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p821 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h16758 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u4)

theorem step28560 (p8 p134 p142 p163 p167 p344 p560 p710 : Prop)
    (h26841 : p142 ∨ p134)
    (h26889 : p710 ∨ p8)
    (h26843 : p167 ∨ p163)
    (h17046 : (¬ p142) ∨ (¬ p167) ∨ (¬ p344) ∨ (¬ p560) ∨ (¬ p710)) : (¬ p344) ∨ (¬ p560) ∨ p134 ∨ p8 ∨ p163 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17046 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)

theorem step28563 (p134 p142 p382 p424 p480 p796 p1325 : Prop)
    (h26891 : p796 ∨ p424)
    (h26841 : p142 ∨ p134)
    (h17282 : (¬ p142) ∨ (¬ p382) ∨ (¬ p480) ∨ (¬ p796) ∨ (¬ p1325)) : p424 ∨ p134 ∨ (¬ p480) ∨ (¬ p382) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p134) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p480 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h17282 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)

theorem step28564 (p2 p84 p134 p142 p186 p424 p481 p495 p499 p582 p595 p616 p796 p1287 : Prop)
    (h26891 : p796 ∨ p424)
    (h26875 : p499 ∨ p495)
    (h26841 : p142 ∨ p134)
    (h26873 : p481 ∨ p2)
    (h26883 : p616 ∨ p595)
    (h17295 : (¬ p84) ∨ (¬ p142) ∨ (¬ p186) ∨ (¬ p481) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p616) ∨ (¬ p796) ∨ (¬ p1287)) : p424 ∨ p495 ∨ (¬ p582) ∨ (¬ p1287) ∨ p134 ∨ p2 ∨ (¬ p186) ∨ p595 ∨ (¬ p84) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u12 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u13 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h17295 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u12)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u13)
  · exact False.elim (q7 u9)
  · exact False.elim (q8 u3)

theorem step28565 (p2 p86 p134 p142 p186 p303 p420 p424 p481 p495 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26841 : p142 ∨ p134)
    (h26873 : p481 ∨ p2)
    (h17296 : (¬ p86) ∨ (¬ p142) ∨ (¬ p186) ∨ (¬ p303) ∨ (¬ p420) ∨ (¬ p481) ∨ (¬ p495) ∨ (¬ p796)) : p424 ∨ (¬ p186) ∨ (¬ p495) ∨ p134 ∨ (¬ p303) ∨ (¬ p86) ∨ p2 ∨ (¬ p420) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17296 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u8)

theorem step28566 (p14 p134 p142 p165 p241 p534 p769 : Prop)
    (h26841 : p142 ∨ p134)
    (h17327 : (¬ p14) ∨ (¬ p142) ∨ (¬ p165) ∨ (¬ p241) ∨ (¬ p534) ∨ (¬ p769)) : (¬ p165) ∨ (¬ p534) ∨ (¬ p769) ∨ p134 ∨ (¬ p14) ∨ (¬ p241) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p165 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17327 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)

theorem step28568 (p134 p142 p163 p167 p344 p883 p897 : Prop)
    (h26841 : p142 ∨ p134)
    (h26843 : p167 ∨ p163)
    (h17361 : (¬ p142) ∨ (¬ p167) ∨ (¬ p344) ∨ (¬ p883) ∨ (¬ p897)) : (¬ p897) ∨ (¬ p883) ∨ (¬ p344) ∨ p134 ∨ p163 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17361 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step28569 (p134 p142 p185 p189 p193 p918 p928 : Prop)
    (h26901 : p928 ∨ p918)
    (h26845 : p193 ∨ p189)
    (h26841 : p142 ∨ p134)
    (h17366 : (¬ p142) ∨ (¬ p185) ∨ (¬ p193) ∨ (¬ p928)) : (¬ p185) ∨ p918 ∨ p189 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p918) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p928 := by
    rcases h26901 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17366 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step28570 (p125 p134 p142 p207 p303 p362 p387 p1325 p1333 : Prop)
    (h26867 : p387 ∨ p303)
    (h26931 : p1333 ∨ p1325)
    (h26865 : p362 ∨ p125)
    (h26841 : p142 ∨ p134)
    (h17552 : (¬ p142) ∨ (¬ p207) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p1333)) : p303 ∨ p1325 ∨ p125 ∨ (¬ p207) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17552 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)

theorem step28571 (p2 p125 p134 p142 p191 p207 p303 p362 p387 p431 p435 : Prop)
    (h26867 : p387 ∨ p303)
    (h26865 : p362 ∨ p125)
    (h26841 : p142 ∨ p134)
    (h17562 : (¬ p2) ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p207) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p431) ∨ (¬ p435)) : (¬ p2) ∨ p303 ∨ (¬ p207) ∨ (¬ p191) ∨ (¬ p431) ∨ p125 ∨ (¬ p435) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h17562 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u6)

theorem step28572 (p6 p12 p134 p142 p561 p1036 p1055 p1061 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26907 : p1036 ∨ p12)
    (h26841 : p142 ∨ p134)
    (h17615 : (¬ p6) ∨ (¬ p142) ∨ (¬ p561) ∨ (¬ p1036) ∨ (¬ p1061)) : p1055 ∨ p12 ∨ (¬ p561) ∨ p134 ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1055) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17615 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step28573 (p134 p142 p207 p303 p368 p387 p438 p687 : Prop)
    (h26867 : p387 ∨ p303)
    (h26841 : p142 ∨ p134)
    (h17623 : (¬ p142) ∨ (¬ p207) ∨ (¬ p368) ∨ (¬ p387) ∨ (¬ p438) ∨ (¬ p687)) : (¬ p687) ∨ p303 ∨ (¬ p438) ∨ (¬ p368) ∨ (¬ p207) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p368 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17623 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u0)

theorem step28575 (p108 p134 p142 p189 p193 p225 p344 p346 p544 : Prop)
    (h26877 : p544 ∨ p225)
    (h26863 : p346 ∨ p344)
    (h26845 : p193 ∨ p189)
    (h26841 : p142 ∨ p134)
    (h17641 : (¬ p108) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p346) ∨ (¬ p544)) : p225 ∨ p344 ∨ (¬ p108) ∨ p189 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17641 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step28576 (p10 p86 p134 p142 p189 p193 p323 p595 p616 p1287 p1325 : Prop)
    (h26845 : p193 ∨ p189)
    (h26883 : p616 ∨ p595)
    (h26841 : p142 ∨ p134)
    (h26861 : p323 ∨ p10)
    (h17642 : (¬ p86) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p323) ∨ (¬ p616) ∨ (¬ p1287) ∨ (¬ p1325)) : p189 ∨ p595 ∨ (¬ p1287) ∨ p134 ∨ (¬ p86) ∨ p10 ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p189) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p595) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h17642 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u6)

theorem step28578 (p86 p134 p142 p161 p189 p193 p1229 p1232 p1449 p1665 : Prop)
    (h26845 : p193 ∨ p189)
    (h26841 : p142 ∨ p134)
    (h26927 : p1232 ∨ p1229)
    (h17798 : (¬ p86) ∨ (¬ p142) ∨ (¬ p161) ∨ (¬ p193) ∨ (¬ p1232) ∨ (¬ p1449) ∨ (¬ p1665)) : (¬ p1665) ∨ p189 ∨ (¬ p161) ∨ (¬ p1449) ∨ p134 ∨ (¬ p86) ∨ p1229 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p1232 := by
    rcases h26927 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h17798 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u0)

theorem step28580 (p134 p142 p207 p310 p344 p1055 p1061 p1076 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26841 : p142 ∨ p134)
    (h17851 : (¬ p142) ∨ (¬ p207) ∨ (¬ p310) ∨ (¬ p344) ∨ (¬ p1061) ∨ (¬ p1076)) : p1055 ∨ (¬ p344) ∨ (¬ p1076) ∨ p134 ∨ (¬ p310) ∨ (¬ p207) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1055) := fun hu => hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17851 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)

theorem step28581 (p3 p10 p134 p142 p163 p167 p323 : Prop)
    (h26843 : p167 ∨ p163)
    (h26861 : p323 ∨ p10)
    (h26841 : p142 ∨ p134)
    (h17885 : (¬ p3) ∨ (¬ p142) ∨ (¬ p167) ∨ (¬ p323)) : (¬ p3) ∨ p163 ∨ p10 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17885 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step28582 (p8 p134 p142 p163 p167 p225 : Prop)
    (h26843 : p167 ∨ p163)
    (h26841 : p142 ∨ p134)
    (h17937 : (¬ p8) ∨ (¬ p142) ∨ (¬ p167) ∨ (¬ p225)) : (¬ p8) ∨ p163 ∨ p134 ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
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
  rcases h17937 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)

theorem step28583 (p6 p134 p142 p188 p790 : Prop)
    (h26841 : p142 ∨ p134)
    (h25846 : (¬ p790) ∨ (¬ p6) ∨ (¬ p142) ∨ (¬ p188)) : (¬ p790) ∨ (¬ p188) ∨ p134 ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25846 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)

theorem step28584 (p18 p134 p142 p382 p815 p1193 p1286 : Prop)
    (h26841 : p142 ∨ p134)
    (h18053 : (¬ p18) ∨ (¬ p142) ∨ (¬ p382) ∨ (¬ p815) ∨ (¬ p1193) ∨ (¬ p1286)) : (¬ p18) ∨ (¬ p1286) ∨ (¬ p815) ∨ (¬ p382) ∨ (¬ p1193) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p815 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18053 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u1)

theorem step28585 (p2 p6 p134 p142 p234 p481 p1187 : Prop)
    (h26921 : p1187 ∨ p234)
    (h26841 : p142 ∨ p134)
    (h26873 : p481 ∨ p2)
    (h18057 : (¬ p6) ∨ (¬ p142) ∨ (¬ p481) ∨ (¬ p1187)) : p234 ∨ p134 ∨ (¬ p6) ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p234) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p134) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1187 := by
    rcases h26921 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18057 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)

theorem step28586 (p108 p134 p142 p163 : Prop)
    (h26841 : p142 ∨ p134)
    (h13328 : (¬ p108) ∨ (¬ p142) ∨ p163) : (¬ p108) ∨ p163 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h13328 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)

theorem step28587 (p41 p134 p142 p1209 p1249 p1253 : Prop)
    (h26841 : p142 ∨ p134)
    (h18331 : (¬ p41) ∨ (¬ p142) ∨ (¬ p1209) ∨ (¬ p1249) ∨ (¬ p1253)) : (¬ p1253) ∨ (¬ p1249) ∨ (¬ p1209) ∨ p134 ∨ (¬ p41) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1253 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18331 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step28588 (p104 p134 p142 p163 p167 p207 p227 p1084 : Prop)
    (h26841 : p142 ∨ p134)
    (h26843 : p167 ∨ p163)
    (h18434 : (¬ p104) ∨ (¬ p142) ∨ (¬ p167) ∨ (¬ p207) ∨ (¬ p227) ∨ (¬ p1084)) : (¬ p104) ∨ (¬ p227) ∨ (¬ p1084) ∨ p134 ∨ (¬ p207) ∨ p163 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18434 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)

theorem step28589 (p18 p134 p142 p191 p423 p1140 p1159 : Prop)
    (h26919 : p1159 ∨ p1140)
    (h26841 : p142 ∨ p134)
    (h18435 : (¬ p18) ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p423) ∨ (¬ p1159)) : p1140 ∨ (¬ p423) ∨ (¬ p191) ∨ p134 ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1140) := fun hu => hn (Or.inl hu)
  have u1 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1159 := by
    rcases h26919 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18435 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)

theorem step28590 (p134 p142 p163 p167 p224 p382 p480 p539 p657 : Prop)
    (h26843 : p167 ∨ p163)
    (h26841 : p142 ∨ p134)
    (h26887 : p657 ∨ p224)
    (h18615 : (¬ p142) ∨ (¬ p167) ∨ (¬ p382) ∨ (¬ p480) ∨ (¬ p539) ∨ (¬ p657)) : (¬ p539) ∨ p163 ∨ p134 ∨ p224 ∨ (¬ p480) ∨ (¬ p382) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p539 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p480 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18615 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u8)

theorem step28591 (p3 p105 p134 p142 p226 p422 p1140 : Prop)
    (h26847 : p226 ∨ p3)
    (h26841 : p142 ∨ p134)
    (h18625 : (¬ p105) ∨ (¬ p142) ∨ (¬ p226) ∨ (¬ p422) ∨ (¬ p1140)) : (¬ p1140) ∨ (¬ p422) ∨ p3 ∨ (¬ p105) ∨ p134 := by
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
  have u2 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18625 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step28592 (p134 p142 p189 p193 p1273 p1349 : Prop)
    (h26841 : p142 ∨ p134)
    (h26845 : p193 ∨ p189)
    (h18741 : (¬ p142) ∨ (¬ p193) ∨ (¬ p1273) ∨ (¬ p1349)) : (¬ p1349) ∨ (¬ p1273) ∨ p134 ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18741 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)

theorem step28593 (p12 p134 p142 p163 p167 p1036 p1076 p1077 : Prop)
    (h26907 : p1036 ∨ p12)
    (h26911 : p1077 ∨ p1076)
    (h26843 : p167 ∨ p163)
    (h26841 : p142 ∨ p134)
    (h18758 : (¬ p142) ∨ (¬ p167) ∨ (¬ p1036) ∨ (¬ p1077)) : p12 ∨ p1076 ∨ p163 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p12) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18758 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step28594 (p105 p134 p142 p165 p557 p1055 p1061 p1115 : Prop)
    (h26909 : p1061 ∨ p1055)
    (h26841 : p142 ∨ p134)
    (h18766 : (¬ p105) ∨ (¬ p142) ∨ (¬ p165) ∨ (¬ p557) ∨ (¬ p1061) ∨ (¬ p1115)) : (¬ p165) ∨ p1055 ∨ (¬ p1115) ∨ (¬ p557) ∨ (¬ p105) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p165 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1055) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18766 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)

theorem step28596 (p10 p86 p134 p142 p189 p193 p323 p382 p603 p614 p1286 : Prop)
    (h26845 : p193 ∨ p189)
    (h26841 : p142 ∨ p134)
    (h26861 : p323 ∨ p10)
    (h18775 : (¬ p86) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p323) ∨ (¬ p382) ∨ (¬ p603) ∨ (¬ p614) ∨ (¬ p1286)) : (¬ p1286) ∨ p189 ∨ p134 ∨ (¬ p614) ∨ p10 ∨ (¬ p86) ∨ (¬ p382) ∨ (¬ p603) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p614 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p603 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18775 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u0)

theorem step28597 (p101 p102 p134 p142 p189 p193 p224 p243 p690 p709 p728 : Prop)
    (h26841 : p142 ∨ p134)
    (h26845 : p193 ∨ p189)
    (h26837 : p102 ∨ p101)
    (h18831 : (¬ p102) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p224) ∨ (¬ p243) ∨ (¬ p690) ∨ (¬ p709) ∨ (¬ p728)) : (¬ p690) ∨ (¬ p709) ∨ p134 ∨ p189 ∨ (¬ p224) ∨ p101 ∨ (¬ p728) ∨ (¬ p243) := by
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
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p243 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18831 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u6)

theorem step28599 (p10 p134 p142 p323 p422 p1140 : Prop)
    (h26861 : p323 ∨ p10)
    (h26841 : p142 ∨ p134)
    (h18877 : (¬ p142) ∨ (¬ p323) ∨ (¬ p422) ∨ (¬ p1140)) : (¬ p422) ∨ (¬ p1140) ∨ p10 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18877 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)

theorem step28600 (p8 p121 p134 p142 p189 p193 p224 p228 p243 p710 : Prop)
    (h26889 : p710 ∨ p8)
    (h26845 : p193 ∨ p189)
    (h26841 : p142 ∨ p134)
    (h18880 : (¬ p121) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p224) ∨ (¬ p228) ∨ (¬ p243) ∨ (¬ p710)) : p8 ∨ (¬ p243) ∨ (¬ p228) ∨ p189 ∨ (¬ p121) ∨ p134 ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p8) := fun hu => hn (Or.inl hu)
  have u1 : p243 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18880 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step28601 (p101 p102 p134 p142 p422 p1140 : Prop)
    (h26837 : p102 ∨ p101)
    (h26841 : p142 ∨ p134)
    (h18883 : (¬ p102) ∨ (¬ p142) ∨ (¬ p422) ∨ (¬ p1140)) : (¬ p422) ∨ (¬ p1140) ∨ p101 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18883 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)

theorem step28602 (p2 p6 p134 p142 p163 p167 p481 : Prop)
    (h26843 : p167 ∨ p163)
    (h26841 : p142 ∨ p134)
    (h26873 : p481 ∨ p2)
    (h18910 : (¬ p6) ∨ (¬ p142) ∨ (¬ p167) ∨ (¬ p481)) : p163 ∨ p134 ∨ (¬ p6) ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p163) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p134) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18910 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)

theorem step28603 (p124 p134 p142 p207 p344 p728 : Prop)
    (h26841 : p142 ∨ p134)
    (h18975 : (¬ p124) ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p344) ∨ (¬ p728)) : (¬ p728) ∨ (¬ p344) ∨ p134 ∨ (¬ p207) ∨ (¬ p124) := by
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
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18975 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step28605 (p18 p134 p142 p419 p424 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26841 : p142 ∨ p134)
    (h19364 : (¬ p18) ∨ (¬ p142) ∨ (¬ p419) ∨ (¬ p796)) : p424 ∨ (¬ p18) ∨ p134 ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19364 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step28606 (p2 p6 p134 p142 p303 p328 p387 p481 : Prop)
    (h26867 : p387 ∨ p303)
    (h26841 : p142 ∨ p134)
    (h26873 : p481 ∨ p2)
    (h19373 : (¬ p6) ∨ (¬ p142) ∨ (¬ p328) ∨ (¬ p387) ∨ (¬ p481)) : p303 ∨ p134 ∨ (¬ p6) ∨ p2 ∨ (¬ p328) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p134) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p328 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19373 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u7)

theorem step28608 (p124 p134 p142 p207 p224 p344 p657 : Prop)
    (h26887 : p657 ∨ p224)
    (h26841 : p142 ∨ p134)
    (h19429 : (¬ p124) ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p344) ∨ (¬ p657)) : (¬ p344) ∨ p224 ∨ (¬ p207) ∨ (¬ p124) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19429 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)

theorem step28609 (p3 p124 p134 p142 p191 p207 p225 p226 p668 p1076 p1077 : Prop)
    (h26847 : p226 ∨ p3)
    (h26911 : p1077 ∨ p1076)
    (h26841 : p142 ∨ p134)
    (h19501 : (¬ p124) ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p207) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p668) ∨ (¬ p1077)) : p3 ∨ p1076 ∨ (¬ p191) ∨ (¬ p124) ∨ p134 ∨ (¬ p668) ∨ (¬ p225) ∨ (¬ p207) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19501 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u9)

theorem step28610 (p125 p134 p142 p207 p224 p303 p362 p387 : Prop)
    (h26867 : p387 ∨ p303)
    (h26865 : p362 ∨ p125)
    (h26841 : p142 ∨ p134)
    (h19511 : (¬ p142) ∨ (¬ p207) ∨ (¬ p224) ∨ (¬ p362) ∨ (¬ p387)) : p303 ∨ (¬ p224) ∨ p125 ∨ (¬ p207) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p303) := fun hu => hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p387 := by
    rcases h26867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19511 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step28611 (p6 p134 p142 p160 p188 p422 p1038 p1325 p1350 : Prop)
    (h26841 : p142 ∨ p134)
    (h25847 : (¬ p160) ∨ (¬ p1325) ∨ (¬ p6) ∨ (¬ p422) ∨ (¬ p1350) ∨ (¬ p188) ∨ (¬ p142) ∨ (¬ p1038)) : (¬ p422) ∨ (¬ p1350) ∨ p134 ∨ (¬ p188) ∨ (¬ p6) ∨ (¬ p1325) ∨ (¬ p1038) ∨ (¬ p160) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1038 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25847 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u6)

theorem step28612 (p6 p134 p142 p163 p167 p225 : Prop)
    (h26843 : p167 ∨ p163)
    (h26841 : p142 ∨ p134)
    (h19541 : (¬ p6) ∨ (¬ p142) ∨ (¬ p167) ∨ (¬ p225)) : p163 ∨ (¬ p225) ∨ p134 ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p163) := fun hu => hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19541 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)

theorem step28613 (p121 p134 p142 p191 p206 p961 : Prop)
    (h26841 : p142 ∨ p134)
    (h19550 : (¬ p121) ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p206) ∨ (¬ p961)) : (¬ p961) ∨ (¬ p121) ∨ (¬ p206) ∨ p134 ∨ (¬ p191) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p961 := by
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
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19550 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)

theorem step28614 (p6 p134 p142 p423 p1140 p1141 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26841 : p142 ∨ p134)
    (h19552 : (¬ p6) ∨ (¬ p142) ∨ (¬ p1140) ∨ (¬ p1141)) : p423 ∨ (¬ p1140) ∨ (¬ p6) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19552 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step28616 (p10 p125 p134 p142 p191 p206 p323 : Prop)
    (h26841 : p142 ∨ p134)
    (h26861 : p323 ∨ p10)
    (h19865 : (¬ p125) ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p206) ∨ (¬ p323)) : (¬ p125) ∨ (¬ p191) ∨ (¬ p206) ∨ p134 ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
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
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19865 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)

theorem step28617 (p6 p134 p142 p1035 p1140 : Prop)
    (h26841 : p142 ∨ p134)
    (h19868 : (¬ p6) ∨ (¬ p142) ∨ (¬ p1035) ∨ (¬ p1140)) : (¬ p1140) ∨ (¬ p1035) ∨ (¬ p6) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19868 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)

theorem step28619 (p134 p142 p207 p227 p980 p1452 : Prop)
    (h26841 : p142 ∨ p134)
    (h19881 : (¬ p142) ∨ (¬ p207) ∨ (¬ p227) ∨ (¬ p980) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p980) ∨ (¬ p227) ∨ (¬ p207) ∨ p134 := by
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
  have u2 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19881 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step28620 (p124 p134 p142 p207 p980 p983 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26903 : p983 ∨ p980)
    (h26841 : p142 ∨ p134)
    (h19882 : (¬ p124) ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p983) ∨ (¬ p1077)) : p1076 ∨ p980 ∨ (¬ p207) ∨ (¬ p124) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19882 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step28623 (p6 p134 p142 p1140 p1211 p1452 : Prop)
    (h26841 : p142 ∨ p134)
    (h19908 : (¬ p6) ∨ (¬ p142) ∨ (¬ p1140) ∨ (¬ p1211) ∨ (¬ p1452)) : (¬ p1452) ∨ (¬ p1211) ∨ (¬ p1140) ∨ (¬ p6) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19908 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step28626 (p6 p8 p134 p142 p710 p836 p840 p1040 p1115 p1140 : Prop)
    (h26889 : p710 ∨ p8)
    (h26841 : p142 ∨ p134)
    (h26895 : p840 ∨ p836)
    (h19975 : (¬ p6) ∨ (¬ p142) ∨ (¬ p710) ∨ (¬ p840) ∨ (¬ p1040) ∨ (¬ p1115) ∨ (¬ p1140)) : (¬ p1115) ∨ p8 ∨ p134 ∨ (¬ p1040) ∨ (¬ p6) ∨ p836 ∨ (¬ p1140) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p8) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1040 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h19975 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u6)

theorem step28628 (p134 p142 p234 p476 p687 p797 p1015 : Prop)
    (h26841 : p142 ∨ p134)
    (h20249 : (¬ p142) ∨ (¬ p234) ∨ (¬ p476) ∨ (¬ p687) ∨ (¬ p797) ∨ (¬ p1015)) : (¬ p687) ∨ (¬ p797) ∨ (¬ p1015) ∨ p134 ∨ (¬ p234) ∨ (¬ p476) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p797 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p476 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20249 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)

theorem step28629 (p8 p105 p134 p142 p192 p225 p544 p556 p710 : Prop)
    (h26877 : p544 ∨ p225)
    (h26841 : p142 ∨ p134)
    (h26889 : p710 ∨ p8)
    (h20256 : (¬ p105) ∨ (¬ p142) ∨ (¬ p192) ∨ (¬ p544) ∨ (¬ p556) ∨ (¬ p710)) : (¬ p556) ∨ (¬ p105) ∨ p225 ∨ (¬ p192) ∨ p134 ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u8 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20256 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u8)

theorem step28630 (p2 p84 p134 p142 p186 p424 p481 p495 p499 p582 p595 p616 p796 p1545 : Prop)
    (h26875 : p499 ∨ p495)
    (h26891 : p796 ∨ p424)
    (h26883 : p616 ∨ p595)
    (h26841 : p142 ∨ p134)
    (h26873 : p481 ∨ p2)
    (h20273 : (¬ p84) ∨ (¬ p142) ∨ (¬ p186) ∨ (¬ p481) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p616) ∨ (¬ p796) ∨ (¬ p1545)) : p495 ∨ p424 ∨ p595 ∨ p134 ∨ p2 ∨ (¬ p1545) ∨ (¬ p186) ∨ (¬ p84) ∨ (¬ p582) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p424) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u11 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u12 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u13 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20273 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u12)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u13)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u10)
  · exact False.elim (q8 u5)

theorem step28631 (p2 p3 p105 p134 p142 p226 p424 p481 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26841 : p142 ∨ p134)
    (h26847 : p226 ∨ p3)
    (h26873 : p481 ∨ p2)
    (h20274 : (¬ p105) ∨ (¬ p142) ∨ (¬ p226) ∨ (¬ p481) ∨ (¬ p796)) : p424 ∨ p134 ∨ (¬ p105) ∨ p3 ∨ p2 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p134) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u7 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20274 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u5)

theorem step28634 (p134 p142 p326 p419 p789 p797 p858 p996 : Prop)
    (h26905 : p996 ∨ p419)
    (h26897 : p858 ∨ p789)
    (h26841 : p142 ∨ p134)
    (h20385 : (¬ p142) ∨ (¬ p326) ∨ (¬ p797) ∨ (¬ p858) ∨ (¬ p996)) : (¬ p797) ∨ p419 ∨ (¬ p326) ∨ p789 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p797 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p419) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p996 := by
    rcases h26905 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p858 := by
    rcases h26897 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h20385 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step28635 (p41 p134 p142 p790 p1385 : Prop)
    (h26841 : p142 ∨ p134)
    (h20386 : (¬ p41) ∨ (¬ p142) ∨ (¬ p790) ∨ (¬ p1385)) : (¬ p790) ∨ (¬ p1385) ∨ p134 ∨ (¬ p41) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h20386 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)

theorem step28636 (p15 p134 p142 p234 p424 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26841 : p142 ∨ p134)
    (h20397 : (¬ p15) ∨ (¬ p142) ∨ (¬ p234) ∨ (¬ p796)) : p424 ∨ p134 ∨ (¬ p15) ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p134) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
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
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h20397 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)

theorem step28638 (p5 p6 p134 p142 p424 p545 p796 p897 p904 p1096 : Prop)
    (h26891 : p796 ∨ p424)
    (h26899 : p904 ∨ p897)
    (h26841 : p142 ∨ p134)
    (h18942 : (¬ p5) ∨ (¬ p6) ∨ (¬ p142) ∨ (¬ p545) ∨ (¬ p796) ∨ (¬ p904) ∨ (¬ p1096)) : (¬ p1096) ∨ p424 ∨ (¬ p6) ∨ p897 ∨ (¬ p545) ∨ p134 ∨ (¬ p5) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p424) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p904 := by
    rcases h26899 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18942 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u0)

theorem step28639 (p6 p104 p134 p142 p163 p167 p1076 : Prop)
    (h26843 : p167 ∨ p163)
    (h26841 : p142 ∨ p134)
    (h19517 : (¬ p6) ∨ (¬ p104) ∨ (¬ p142) ∨ (¬ p167) ∨ (¬ p1076)) : (¬ p104) ∨ p163 ∨ (¬ p6) ∨ (¬ p1076) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19517 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)

theorem step28640 (p6 p8 p134 p142 p163 p167 p188 p224 p239 p657 p1325 p1333 : Prop)
    (h26887 : p657 ∨ p224)
    (h26931 : p1333 ∨ p1325)
    (h26841 : p142 ∨ p134)
    (h26843 : p167 ∨ p163)
    (h19542 : (¬ p6) ∨ (¬ p8) ∨ (¬ p142) ∨ (¬ p167) ∨ (¬ p188) ∨ (¬ p239) ∨ (¬ p657) ∨ (¬ p1333)) : (¬ p8) ∨ p224 ∨ p1325 ∨ p134 ∨ (¬ p188) ∨ (¬ p239) ∨ (¬ p6) ∨ p163 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p239 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h19542 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u9)

theorem step28641 (p6 p88 p134 p142 p188 p424 p545 p615 p687 p734 p796 p1389 : Prop)
    (h26891 : p796 ∨ p424)
    (h26841 : p142 ∨ p134)
    (h19547 : (¬ p6) ∨ (¬ p88) ∨ (¬ p142) ∨ (¬ p188) ∨ (¬ p545) ∨ (¬ p615) ∨ (¬ p687) ∨ (¬ p734) ∨ (¬ p796) ∨ (¬ p1389)) : (¬ p615) ∨ (¬ p1389) ∨ p424 ∨ (¬ p188) ∨ (¬ p88) ∨ (¬ p6) ∨ p134 ∨ (¬ p734) ∨ (¬ p687) ∨ (¬ p545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p615 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p424) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p88 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19547 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u1)

theorem step28642 (p6 p16 p134 p142 p188 p422 p595 p1004 p1286 : Prop)
    (h26841 : p142 ∨ p134)
    (h19558 : (¬ p6) ∨ (¬ p16) ∨ (¬ p142) ∨ (¬ p188) ∨ (¬ p422) ∨ (¬ p595) ∨ (¬ p1004) ∨ (¬ p1286)) : (¬ p422) ∨ (¬ p1004) ∨ p134 ∨ (¬ p6) ∨ (¬ p16) ∨ (¬ p188) ∨ (¬ p1286) ∨ (¬ p595) := by
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
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p16 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19558 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u6)

theorem step28643 (p2 p6 p63 p85 p134 p142 p481 p542 p836 p918 : Prop)
    (h26835 : p85 ∨ p63)
    (h26873 : p481 ∨ p2)
    (h26841 : p142 ∨ p134)
    (h19905 : (¬ p6) ∨ (¬ p85) ∨ (¬ p142) ∨ (¬ p481) ∨ (¬ p542) ∨ (¬ p836) ∨ (¬ p918)) : (¬ p836) ∨ p63 ∨ (¬ p542) ∨ p2 ∨ (¬ p918) ∨ (¬ p6) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p63) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p85 := by
    rcases h26835 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19905 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u4)

theorem step28644 (p8 p121 p134 p142 p189 p193 p344 p346 p1055 p1081 : Prop)
    (h26863 : p346 ∨ p344)
    (h26845 : p193 ∨ p189)
    (h26841 : p142 ∨ p134)
    (h18879 : (¬ p8) ∨ (¬ p121) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p346) ∨ (¬ p1055) ∨ (¬ p1081)) : (¬ p1055) ∨ (¬ p121) ∨ p344 ∨ p189 ∨ p134 ∨ (¬ p8) ∨ (¬ p1081) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18879 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u6)

theorem step28645 (p8 p105 p134 p142 p165 p557 p836 : Prop)
    (h26841 : p142 ∨ p134)
    (h20259 : (¬ p8) ∨ (¬ p105) ∨ (¬ p142) ∨ (¬ p165) ∨ (¬ p557) ∨ (¬ p836)) : (¬ p165) ∨ (¬ p557) ∨ (¬ p8) ∨ p134 ∨ (¬ p836) ∨ (¬ p105) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p165 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h20259 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u4)

theorem step28647 (p14 p15 p134 p142 p163 p167 : Prop)
    (h26843 : p167 ∨ p163)
    (h26841 : p142 ∨ p134)
    (h17360 : (¬ p14) ∨ (¬ p15) ∨ (¬ p142) ∨ (¬ p167)) : (¬ p14) ∨ (¬ p15) ∨ p163 ∨ p134 := by
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
  have u2 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17360 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step28648 (p14 p18 p134 p142 p225 p544 : Prop)
    (h26877 : p544 ∨ p225)
    (h26841 : p142 ∨ p134)
    (h19866 : (¬ p14) ∨ (¬ p18) ∨ (¬ p142) ∨ (¬ p544)) : p225 ∨ (¬ p14) ∨ (¬ p18) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p544 := by
    rcases h26877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19866 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step28649 (p3 p14 p18 p134 p142 p191 p226 : Prop)
    (h26847 : p226 ∨ p3)
    (h26841 : p142 ∨ p134)
    (h19879 : (¬ p14) ∨ (¬ p18) ∨ (¬ p142) ∨ (¬ p191) ∨ (¬ p226)) : p3 ∨ (¬ p14) ∨ (¬ p18) ∨ (¬ p191) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p226 := by
    rcases h26847 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19879 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)

theorem step28651 (p18 p47 p134 p142 : Prop)
    (h26841 : p142 ∨ p134)
    (h13198 : (¬ p18) ∨ (¬ p47) ∨ (¬ p142)) : (¬ p18) ∨ (¬ p47) ∨ p134 := by
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
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h13198 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step28655 (p2 p125 p134 p142 p420 p424 p481 p494 p601 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26881 : p601 ∨ p420)
    (h26841 : p142 ∨ p134)
    (h26873 : p481 ∨ p2)
    (h25851 : (¬ p601) ∨ (¬ p796) ∨ (¬ p125) ∨ (¬ p142) ∨ (¬ p494) ∨ (¬ p481)) : p424 ∨ (¬ p125) ∨ p420 ∨ p134 ∨ p2 ∨ (¬ p494) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p601 := by
    rcases h26881 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25851 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u9)

theorem step28656 (p20 p125 p134 p142 p207 p362 p420 : Prop)
    (h26841 : p142 ∨ p134)
    (h26865 : p362 ∨ p125)
    (h25852 : (¬ p420) ∨ (¬ p362) ∨ (¬ p142) ∨ (¬ p207) ∨ (¬ p20)) : (¬ p420) ∨ (¬ p20) ∨ p134 ∨ p125 ∨ (¬ p207) := by
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
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25852 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)

theorem step28657 (p15 p21 p134 p142 p495 : Prop)
    (h26841 : p142 ∨ p134)
    (h25853 : (¬ p21) ∨ (¬ p495) ∨ (¬ p15) ∨ (¬ p142)) : (¬ p15) ∨ (¬ p495) ∨ p134 ∨ (¬ p21) := by
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
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25853 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)

theorem step28658 (p6 p41 p87 p134 p142 p188 : Prop)
    (h26841 : p142 ∨ p134)
    (h16267 : (¬ p6) ∨ (¬ p41) ∨ (¬ p87) ∨ (¬ p142) ∨ (¬ p188)) : (¬ p41) ∨ (¬ p188) ∨ p134 ∨ (¬ p6) ∨ (¬ p87) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h16267 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)

theorem step28659 (p41 p89 p134 p142 p185 p237 p918 : Prop)
    (h26851 : p237 ∨ p185)
    (h26841 : p142 ∨ p134)
    (h17257 : (¬ p41) ∨ (¬ p89) ∨ (¬ p142) ∨ (¬ p237) ∨ (¬ p918)) : (¬ p918) ∨ (¬ p41) ∨ p185 ∨ (¬ p89) ∨ p134 := by
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
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h17257 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step28660 (p41 p63 p124 p134 p142 p304 p344 p346 p734 : Prop)
    (h26859 : p304 ∨ p124)
    (h26863 : p346 ∨ p344)
    (h26841 : p142 ∨ p134)
    (h25854 : (¬ p41) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p142) ∨ (¬ p63) ∨ (¬ p734)) : p124 ∨ p344 ∨ (¬ p41) ∨ (¬ p734) ∨ p134 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25854 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)

theorem step28661 (p41 p89 p134 p142 p1249 p1346 : Prop)
    (h26841 : p142 ∨ p134)
    (h18374 : (¬ p41) ∨ (¬ p89) ∨ (¬ p142) ∨ (¬ p1249) ∨ (¬ p1346)) : (¬ p1346) ∨ (¬ p1249) ∨ (¬ p41) ∨ (¬ p89) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1249 := by
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
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18374 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step28662 (p41 p63 p124 p134 p142 p224 p304 p344 p346 : Prop)
    (h26859 : p304 ∨ p124)
    (h26863 : p346 ∨ p344)
    (h26841 : p142 ∨ p134)
    (h25855 : (¬ p41) ∨ (¬ p304) ∨ (¬ p142) ∨ (¬ p224) ∨ (¬ p346) ∨ (¬ p63)) : p124 ∨ p344 ∨ p134 ∨ (¬ p41) ∨ (¬ p224) ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25855 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u5)

theorem step28664 (p10 p41 p63 p134 p142 p323 : Prop)
    (h26841 : p142 ∨ p134)
    (h26861 : p323 ∨ p10)
    (h18567 : (¬ p41) ∨ (¬ p63) ∨ (¬ p142) ∨ (¬ p323)) : (¬ p41) ∨ p134 ∨ p10 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p134) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18567 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step28665 (p20 p101 p102 p134 p142 p633 p636 : Prop)
    (h26885 : p636 ∨ p633)
    (h26837 : p102 ∨ p101)
    (h26841 : p142 ∨ p134)
    (h25856 : (¬ p636) ∨ (¬ p20) ∨ (¬ p142) ∨ (¬ p102)) : p633 ∨ p101 ∨ p134 ∨ (¬ p20) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p20 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25856 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)

theorem step28666 (p20 p101 p102 p124 p134 p142 p304 p425 : Prop)
    (h26859 : p304 ∨ p124)
    (h26837 : p102 ∨ p101)
    (h26841 : p142 ∨ p134)
    (h25857 : (¬ p304) ∨ (¬ p425) ∨ (¬ p102) ∨ (¬ p142) ∨ (¬ p20)) : p124 ∨ p101 ∨ p134 ∨ (¬ p20) ∨ (¬ p425) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p20 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p425 := by
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
  have u7 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25857 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u3)

theorem step28667 (p18 p43 p90 p134 p142 p189 p193 : Prop)
    (h26586 : p90)
    (h26845 : p193 ∨ p189)
    (h26841 : p142 ∨ p134)
    (h17247 : (¬ p18) ∨ (¬ p43) ∨ (¬ p90) ∨ (¬ p142) ∨ (¬ p193)) : (¬ p43) ∨ (¬ p18) ∨ p189 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p90 := by
    exact h26586
  have u5 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17247 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step28668 (p41 p63 p101 p102 p134 p142 : Prop)
    (h26837 : p102 ∨ p101)
    (h26841 : p142 ∨ p134)
    (h17415 : (¬ p41) ∨ (¬ p63) ∨ (¬ p102) ∨ (¬ p142)) : (¬ p41) ∨ p101 ∨ p134 ∨ (¬ p63) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h17415 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)

theorem step28669 (p48 p63 p134 p142 p422 p423 : Prop)
    (h26841 : p142 ∨ p134)
    (h18564 : (¬ p48) ∨ (¬ p63) ∨ (¬ p142) ∨ (¬ p422) ∨ (¬ p423)) : (¬ p422) ∨ (¬ p48) ∨ (¬ p423) ∨ (¬ p63) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18564 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u2)

theorem step28670 (p41 p63 p121 p134 p142 : Prop)
    (h26841 : p142 ∨ p134)
    (h18566 : (¬ p41) ∨ (¬ p63) ∨ (¬ p121) ∨ (¬ p142)) : (¬ p41) ∨ (¬ p121) ∨ (¬ p63) ∨ p134 := by
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
  have u2 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18566 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)

theorem step28671 (p41 p63 p125 p134 p142 p303 p1325 : Prop)
    (h26841 : p142 ∨ p134)
    (h25858 : (¬ p41) ∨ (¬ p1325) ∨ (¬ p63) ∨ (¬ p142) ∨ (¬ p303) ∨ (¬ p125)) : (¬ p41) ∨ (¬ p125) ∨ p134 ∨ (¬ p303) ∨ (¬ p1325) ∨ (¬ p63) := by
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
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h25858 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u1)

theorem step28674 (p86 p101 p102 p134 p142 p189 p193 p224 p897 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26845 : p193 ∨ p189)
    (h26841 : p142 ∨ p134)
    (h26837 : p102 ∨ p101)
    (h18833 : (¬ p86) ∨ (¬ p102) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p224) ∨ (¬ p897) ∨ (¬ p1099)) : p1096 ∨ p189 ∨ (¬ p897) ∨ (¬ p86) ∨ (¬ p224) ∨ p134 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1096) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h18833 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u7)

theorem step28675 (p15 p69 p84 p134 p142 p189 p193 p495 p499 p582 p1689 p1710 : Prop)
    (h26845 : p193 ∨ p189)
    (h26875 : p499 ∨ p495)
    (h26833 : p69 ∨ p15)
    (h26841 : p142 ∨ p134)
    (h18705 : (¬ p69) ∨ (¬ p84) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p499) ∨ (¬ p582) ∨ (¬ p1689) ∨ (¬ p1710)) : (¬ p1710) ∨ (¬ p1689) ∨ (¬ p84) ∨ p189 ∨ p495 ∨ (¬ p582) ∨ p15 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1689 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p499 := by
    rcases h26875 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18705 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u0)

theorem step28676 (p15 p69 p84 p134 p142 p189 p193 p423 p929 p1096 p1141 p1209 : Prop)
    (h26917 : p1141 ∨ p423)
    (h26845 : p193 ∨ p189)
    (h26841 : p142 ∨ p134)
    (h26833 : p69 ∨ p15)
    (h18750 : (¬ p69) ∨ (¬ p84) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p929) ∨ (¬ p1096) ∨ (¬ p1141) ∨ (¬ p1209)) : p423 ∨ (¬ p929) ∨ (¬ p1209) ∨ (¬ p84) ∨ p189 ∨ p134 ∨ (¬ p1096) ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p423) := fun hu => hn (Or.inl hu)
  have u1 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1141 := by
    rcases h26917 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u10 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u11 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18750 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u11)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u2)

theorem step28677 (p48 p125 p134 p142 p303 p425 p582 p1325 p1711 p1712 : Prop)
    (h26841 : p142 ∨ p134)
    (h18739 : (¬ p48) ∨ (¬ p125) ∨ (¬ p142) ∨ (¬ p303) ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p1325) ∨ (¬ p1711) ∨ (¬ p1712)) : (¬ p1711) ∨ (¬ p1712) ∨ (¬ p1325) ∨ (¬ p125) ∨ (¬ p425) ∨ (¬ p48) ∨ (¬ p582) ∨ p134 ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1711 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1712 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18739 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u0)
  · exact False.elim (q8 u1)

theorem step28678 (p3 p121 p134 p142 p163 p167 : Prop)
    (h26843 : p167 ∨ p163)
    (h26841 : p142 ∨ p134)
    (h16812 : (¬ p3) ∨ (¬ p121) ∨ (¬ p142) ∨ (¬ p167)) : (¬ p3) ∨ p163 ∨ p134 ∨ (¬ p121) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p121 := by
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
  rcases h16812 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step28679 (p3 p84 p134 p142 p163 p167 p186 p495 p595 p1394 : Prop)
    (h26843 : p167 ∨ p163)
    (h26841 : p142 ∨ p134)
    (h25859 : (¬ p167) ∨ (¬ p1394) ∨ (¬ p142) ∨ (¬ p84) ∨ (¬ p495) ∨ (¬ p186) ∨ (¬ p3) ∨ (¬ p595)) : (¬ p186) ∨ p163 ∨ (¬ p3) ∨ (¬ p595) ∨ (¬ p1394) ∨ (¬ p495) ∨ (¬ p84) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1394 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h25859 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u3)

theorem step28680 (p3 p6 p134 p142 p172 p1074 p1096 p1099 p1115 p1116 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26915 : p1116 ∨ p1115)
    (h26841 : p142 ∨ p134)
    (h19416 : (¬ p3) ∨ (¬ p6) ∨ (¬ p142) ∨ (¬ p172) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1116)) : (¬ p172) ∨ p1096 ∨ (¬ p6) ∨ (¬ p3) ∨ (¬ p1074) ∨ p1115 ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p1115) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p1116 := by
    rcases h26915 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u9 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19416 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)

theorem step28681 (p3 p6 p134 p142 p172 p836 p840 p897 p1096 p1099 : Prop)
    (h26913 : p1099 ∨ p1096)
    (h26895 : p840 ∨ p836)
    (h26841 : p142 ∨ p134)
    (h19904 : (¬ p3) ∨ (¬ p6) ∨ (¬ p142) ∨ (¬ p172) ∨ (¬ p840) ∨ (¬ p897) ∨ (¬ p1099)) : (¬ p172) ∨ p1096 ∨ (¬ p6) ∨ (¬ p3) ∨ p836 ∨ (¬ p897) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1099 := by
    rcases h26913 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p840 := by
    rcases h26895 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h19904 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u7)

theorem step28682 (p3 p6 p14 p134 p142 p229 : Prop)
    (h26849 : p229 ∨ p14)
    (h26841 : p142 ∨ p134)
    (h19972 : (¬ p3) ∨ (¬ p6) ∨ (¬ p142) ∨ (¬ p229)) : p14 ∨ (¬ p3) ∨ p134 ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p14) := fun hu => hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p229 := by
    rcases h26849 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19972 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step28683 (p84 p105 p134 p142 p166 p189 p193 p918 : Prop)
    (h26845 : p193 ∨ p189)
    (h26841 : p142 ∨ p134)
    (h20167 : (¬ p84) ∨ (¬ p105) ∨ (¬ p142) ∨ (¬ p166) ∨ (¬ p193) ∨ (¬ p918)) : (¬ p105) ∨ (¬ p918) ∨ (¬ p84) ∨ p189 ∨ (¬ p166) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p166 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h20167 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)

theorem step28684 (p104 p124 p134 p142 p163 p167 p213 : Prop)
    (h26843 : p167 ∨ p163)
    (h26841 : p142 ∨ p134)
    (h18811 : (¬ p104) ∨ (¬ p124) ∨ (¬ p142) ∨ (¬ p167) ∨ (¬ p213)) : (¬ p104) ∨ p163 ∨ p134 ∨ (¬ p124) ∨ (¬ p213) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18811 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)

theorem step28686 (p8 p84 p101 p102 p134 p142 p189 p193 p224 p710 p929 p1102 p1325 : Prop)
    (h26889 : p710 ∨ p8)
    (h26845 : p193 ∨ p189)
    (h26841 : p142 ∨ p134)
    (h26837 : p102 ∨ p101)
    (h18830 : (¬ p84) ∨ (¬ p102) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p224) ∨ (¬ p710) ∨ (¬ p929) ∨ (¬ p1102) ∨ (¬ p1325)) : p8 ∨ (¬ p1102) ∨ (¬ p929) ∨ p189 ∨ (¬ p84) ∨ (¬ p224) ∨ (¬ p1325) ∨ p134 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p8) := fun hu => hn (Or.inl hu)
  have u1 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p84 := by
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
  have u7 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u12 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h18830 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u12)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u6)

theorem step28687 (p84 p101 p102 p134 p142 p189 p193 p635 p929 : Prop)
    (h26845 : p193 ∨ p189)
    (h26841 : p142 ∨ p134)
    (h26837 : p102 ∨ p101)
    (h18872 : (¬ p84) ∨ (¬ p102) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p635) ∨ (¬ p929)) : (¬ p635) ∨ (¬ p929) ∨ (¬ p84) ∨ p189 ∨ p134 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p635 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u8 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h18872 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u1)

theorem step28688 (p84 p101 p102 p134 p142 p189 p193 p595 p616 p929 p1096 p1287 : Prop)
    (h26883 : p616 ∨ p595)
    (h26841 : p142 ∨ p134)
    (h26845 : p193 ∨ p189)
    (h26837 : p102 ∨ p101)
    (h18882 : (¬ p84) ∨ (¬ p102) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p616) ∨ (¬ p929) ∨ (¬ p1096) ∨ (¬ p1287)) : (¬ p929) ∨ (¬ p84) ∨ p595 ∨ p134 ∨ (¬ p1287) ∨ (¬ p1096) ∨ p189 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p595) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p616 := by
    rcases h26883 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p102 := by
    rcases h26837 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h18882 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u11)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u4)

theorem step28690 (p8 p84 p121 p134 p142 p189 p193 p224 p228 p710 p929 p1102 : Prop)
    (h26889 : p710 ∨ p8)
    (h26845 : p193 ∨ p189)
    (h26841 : p142 ∨ p134)
    (h18873 : (¬ p84) ∨ (¬ p121) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p224) ∨ (¬ p228) ∨ (¬ p710) ∨ (¬ p929) ∨ (¬ p1102)) : p8 ∨ (¬ p929) ∨ (¬ p84) ∨ p189 ∨ p134 ∨ (¬ p121) ∨ (¬ p1102) ∨ (¬ p228) ∨ (¬ p224) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p8) := fun hu => hn (Or.inl hu)
  have u1 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p710 := by
    rcases h26889 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18873 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u11)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u1)
  · exact False.elim (q8 u6)

theorem step28692 (p15 p18 p69 p134 p142 p163 p167 : Prop)
    (h26843 : p167 ∨ p163)
    (h26841 : p142 ∨ p134)
    (h26833 : p69 ∨ p15)
    (h18928 : (¬ p18) ∨ (¬ p69) ∨ (¬ p142) ∨ (¬ p167)) : (¬ p18) ∨ p163 ∨ p134 ∨ p15 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p15) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p167 := by
    rcases h26843 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18928 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)

theorem step28694 (p15 p18 p69 p134 p142 p424 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26833 : p69 ∨ p15)
    (h26841 : p142 ∨ p134)
    (h19546 : (¬ p18) ∨ (¬ p69) ∨ (¬ p142) ∨ (¬ p796)) : p424 ∨ p15 ∨ (¬ p18) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p15) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p69 := by
    rcases h26833 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h19546 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u4)

theorem step28695 (p3 p6 p107 p134 p142 p344 : Prop)
    (h26841 : p142 ∨ p134)
    (h17564 : (¬ p3) ∨ (¬ p6) ∨ (¬ p107) ∨ (¬ p142) ∨ (¬ p344)) : (¬ p344) ∨ (¬ p107) ∨ (¬ p6) ∨ p134 ∨ (¬ p3) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h17564 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step28696 (p3 p6 p107 p134 p142 p1076 p1077 : Prop)
    (h26911 : p1077 ∨ p1076)
    (h26841 : p142 ∨ p134)
    (h19411 : (¬ p3) ∨ (¬ p6) ∨ (¬ p107) ∨ (¬ p142) ∨ (¬ p1077)) : p1076 ∨ (¬ p107) ∨ p134 ∨ (¬ p3) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p3 := by
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
    · exact False.elim (u0 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19411 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u5)

theorem step28697 (p3 p6 p107 p134 p142 p756 : Prop)
    (h26841 : p142 ∨ p134)
    (h19974 : (¬ p3) ∨ (¬ p6) ∨ (¬ p107) ∨ (¬ p142) ∨ (¬ p756)) : (¬ p756) ∨ (¬ p107) ∨ p134 ∨ (¬ p3) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h19974 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)

theorem step28698 (p2 p134 p142 p344 p346 p424 p481 p495 p633 p636 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26885 : p636 ∨ p633)
    (h26863 : p346 ∨ p344)
    (h26873 : p481 ∨ p2)
    (h26841 : p142 ∨ p134)
    (h25861 : (¬ p796) ∨ (¬ p495) ∨ (¬ p142) ∨ (¬ p636) ∨ (¬ p346) ∨ (¬ p481)) : p424 ∨ p633 ∨ p344 ∨ p2 ∨ (¬ p495) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p633) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p636 := by
    rcases h26885 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p346 := by
    rcases h26863 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u9 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u10 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h25861 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)

theorem step28699 (p2 p124 p134 p142 p304 p424 p481 p494 p633 p796 : Prop)
    (h26891 : p796 ∨ p424)
    (h26841 : p142 ∨ p134)
    (h26859 : p304 ∨ p124)
    (h26873 : p481 ∨ p2)
    (h25862 : (¬ p494) ∨ (¬ p796) ∨ (¬ p633) ∨ (¬ p481) ∨ (¬ p142) ∨ (¬ p304)) : p424 ∨ p134 ∨ (¬ p494) ∨ p124 ∨ p2 ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p424) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p134) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p124) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p796 := by
    rcases h26891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u8 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u9 : p481 := by
    rcases h26873 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h25862 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)

theorem step28701 (p10 p134 p142 p171 p185 p224 p237 p323 p347 p382 p657 p815 : Prop)
    (h26851 : p237 ∨ p185)
    (h26887 : p657 ∨ p224)
    (h26841 : p142 ∨ p134)
    (h26861 : p323 ∨ p10)
    (h20327 : (¬ p142) ∨ (¬ p171) ∨ (¬ p237) ∨ (¬ p323) ∨ (¬ p347) ∨ (¬ p382) ∨ (¬ p657) ∨ (¬ p815)) : (¬ p171) ∨ p185 ∨ p224 ∨ p134 ∨ (¬ p815) ∨ (¬ p382) ∨ p10 ∨ (¬ p347) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p224) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p815 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u9 : p657 := by
    rcases h26887 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u10 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p323 := by
    rcases h26861 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h20327 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u9)
  · exact False.elim (q7 u4)

theorem step28702 (p18 p43 p134 p142 p1385 p1393 : Prop)
    (h26933 : p1393 ∨ p1385)
    (h26841 : p142 ∨ p134)
    (h25863 : (¬ p1393) ∨ (¬ p43) ∨ (¬ p18) ∨ (¬ p142)) : (¬ p18) ∨ p1385 ∨ (¬ p43) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1385) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p43 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25863 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u5)

theorem step28705 (p20 p134 p142 p207 p227 p455 p456 : Prop)
    (h26871 : p456 ∨ p455)
    (h26841 : p142 ∨ p134)
    (h25865 : (¬ p456) ∨ (¬ p207) ∨ (¬ p20) ∨ (¬ p142) ∨ (¬ p227)) : p455 ∨ (¬ p227) ∨ (¬ p20) ∨ p134 ∨ (¬ p207) := by
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
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p456 := by
    rcases h26871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25865 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)

theorem step28706 (p20 p134 p142 p1604 p1665 : Prop)
    (h26841 : p142 ∨ p134)
    (h25866 : (¬ p1665) ∨ (¬ p1604) ∨ (¬ p20) ∨ (¬ p142)) : (¬ p1604) ∨ (¬ p1665) ∨ (¬ p20) ∨ p134 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1604 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p20 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h25866 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)

theorem step28708 (p134 p142 p1035 p1209 p1252 p1489 : Prop)
    (h26841 : p142 ∨ p134)
    (h18334 : (¬ p142) ∨ (¬ p1035) ∨ (¬ p1209) ∨ (¬ p1252) ∨ (¬ p1489)) : (¬ p1252) ∨ (¬ p1035) ∨ p134 ∨ (¬ p1209) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1252 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p134) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p142 := by
    rcases h26841 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18334 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u4)

theorem step28709 (p14 p18 p107 p124 p209 p304 : Prop)
    (h26859 : p304 ∨ p124)
    (h17455 : (¬ p14) ∨ (¬ p18) ∨ (¬ p107) ∨ (¬ p209) ∨ (¬ p304)) : p124 ∨ (¬ p107) ∨ (¬ p209) ∨ (¬ p14) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p209 := by
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
  have u5 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17455 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)

theorem step28710 (p12 p107 p124 p125 p304 p348 p362 p664 p1036 : Prop)
    (h26859 : p304 ∨ p124)
    (h26865 : p362 ∨ p125)
    (h26907 : p1036 ∨ p12)
    (h19818 : (¬ p107) ∨ (¬ p304) ∨ (¬ p348) ∨ (¬ p362) ∨ (¬ p664) ∨ (¬ p1036)) : p124 ∨ (¬ p348) ∨ (¬ p664) ∨ p125 ∨ p12 ∨ (¬ p107) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p362 := by
    rcases h26865 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h19818 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u8)

theorem step28711 (p12 p38 p49 p107 p124 p206 p304 p980 p1022 p1036 p1330 p1385 p1393 : Prop)
    (h26859 : p304 ∨ p124)
    (h26907 : p1036 ∨ p12)
    (h26933 : p1393 ∨ p1385)
    (h16681 : (¬ p38) ∨ (¬ p49) ∨ (¬ p107) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p980) ∨ (¬ p1022) ∨ (¬ p1036) ∨ (¬ p1330) ∨ (¬ p1393)) : p124 ∨ p12 ∨ (¬ p1330) ∨ p1385 ∨ (¬ p1022) ∨ (¬ p980) ∨ (¬ p107) ∨ (¬ p206) ∨ (¬ p38) ∨ (¬ p49) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p304 := by
    rcases h26859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u11 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u12 : p1393 := by
    rcases h26933 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h16681 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u11)
  · exact False.elim (q8 u2)
  · exact False.elim (q9 u12)

theorem step28712 (p107 p225 p344 p544 : Prop)
    (h26876 : (¬ p225) ∨ (¬ p544))
    (h12476 : (¬ p107) ∨ (¬ p344) ∨ p544) : (¬ p344) ∨ (¬ p107) ∨ (¬ p225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p544) := by
    rcases h26876 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h12476 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (u3 q2)

theorem step28714 (p12 p107 p1036 p1076 : Prop)
    (h26907 : p1036 ∨ p12)
    (h15114 : (¬ p107) ∨ (¬ p1036) ∨ p1076) : p1076 ∨ (¬ p107) ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p12) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h15114 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (u0 q2)

theorem step28715 (p12 p107 p1036 p1076 p1077 : Prop)
    (h26907 : p1036 ∨ p12)
    (h26911 : p1077 ∨ p1076)
    (h9379 : (¬ p107) ∨ (¬ p1036) ∨ (¬ p1077)) : p12 ∨ p1076 ∨ (¬ p107) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p12) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p1036 := by
    rcases h26907 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1077 := by
    rcases h26911 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  rcases h9379 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)

theorem step28717 (p107 p121 p134 p163 p1080 p1206 : Prop)
    (h26923 : p1206 ∨ p121)
    (h16979 : (¬ p107) ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p1080) ∨ (¬ p1206)) : p121 ∨ (¬ p163) ∨ (¬ p134) ∨ (¬ p107) ∨ (¬ p1080) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1206 := by
    rcases h26923 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h16979 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)

theorem step28718 (p23 p107 p134 p163 p633 p636 : Prop)
    (h26885 : p636 ∨ p633)
    (h19367 : (¬ p23) ∨ (¬ p107) ∨ (¬ p134) ∨ (¬ p163) ∨ (¬ p636)) : p633 ∨ (¬ p163) ∨ (¬ p23) ∨ (¬ p107) ∨ (¬ p134) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p107 := by
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
  rcases h19367 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u5)

theorem step28719 (p11 p126 p381 p1443 : Prop)
    (h26935 : p1443 ∨ p11)
    (h10731 : p126 ∨ (¬ p381) ∨ (¬ p1443)) : p126 ∨ (¬ p381) ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p126) := fun hu => hn (Or.inl hu)
  have u1 : p381 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1443 := by
    rcases h26935 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h10731 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)

theorem step28721 (p10 p121 p381 p1206 : Prop)
    (h26922 : (¬ p121) ∨ (¬ p1206))
    (h13849 : (¬ p10) ∨ (¬ p381) ∨ p1206) : (¬ p10) ∨ (¬ p381) ∨ (¬ p121) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p381 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p1206) := by
    rcases h26922 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h13849 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u3 q2)

theorem step28724 (p17 p256 p1349 p1496 : Prop)
    (h26853 : p256 ∨ p17)
    (h13598 : (¬ p256) ∨ (¬ p1349) ∨ (¬ p1496)) : (¬ p1349) ∨ (¬ p1496) ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p256 := by
    rcases h26853 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h13598 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)

theorem step28725 (p790 p814 p862 p1349 : Prop)
    (h26892 : (¬ p790) ∨ (¬ p814))
    (h15761 : p814 ∨ (¬ p862) ∨ (¬ p1349)) : (¬ p862) ∨ (¬ p1349) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p862 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p814) := by
    rcases h26892 with q0 | q1
    · exact False.elim (q0 u2)
    · exact q1
  rcases h15761 with q0 | q1 | q2
  · exact False.elim (u3 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)

theorem step28726 (p189 p193 p1035 p1349 p1489 : Prop)
    (h26845 : p193 ∨ p189)
    (h18714 : (¬ p193) ∨ (¬ p1035) ∨ (¬ p1349) ∨ (¬ p1489)) : (¬ p1035) ∨ (¬ p1349) ∨ p189 ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h18714 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)

theorem step28727 (p189 p193 p1250 p1349 : Prop)
    (h26845 : p193 ∨ p189)
    (h12194 : (¬ p193) ∨ (¬ p1250) ∨ (¬ p1349)) : (¬ p1250) ∨ (¬ p1349) ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1250 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h12194 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)

theorem step28728 (p189 p193 p1253 p1325 p1333 p1349 p1465 : Prop)
    (h26845 : p193 ∨ p189)
    (h26931 : p1333 ∨ p1325)
    (h18286 : (¬ p193) ∨ (¬ p1253) ∨ (¬ p1333) ∨ (¬ p1349) ∨ (¬ p1465)) : (¬ p1253) ∨ (¬ p1349) ∨ (¬ p1465) ∨ p189 ∨ p1325 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1253 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1325) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p1333 := by
    rcases h26931 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18286 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)

theorem step28729 (p41 p45 p189 p193 p1253 p1349 p1465 : Prop)
    (h26831 : p45 ∨ p41)
    (h26845 : p193 ∨ p189)
    (h18289 : (¬ p45) ∨ (¬ p193) ∨ (¬ p1253) ∨ (¬ p1349) ∨ (¬ p1465)) : (¬ p1253) ∨ (¬ p1349) ∨ p41 ∨ p189 ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1253 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p41) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h18289 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)

theorem step28731 (p185 p237 p1122 p1349 : Prop)
    (h26851 : p237 ∨ p185)
    (h12099 : (¬ p237) ∨ (¬ p1122) ∨ (¬ p1349)) : (¬ p1349) ∨ (¬ p1122) ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1122 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p237 := by
    rcases h26851 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h12099 with q0 | q1 | q2
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)

theorem step28733 (p41 p45 p83 p134 p1273 p1349 : Prop)
    (h26831 : p45 ∨ p41)
    (h17065 : (¬ p45) ∨ (¬ p83) ∨ (¬ p134) ∨ (¬ p1273) ∨ (¬ p1349)) : p41 ∨ (¬ p1273) ∨ (¬ p134) ∨ (¬ p83) ∨ (¬ p1349) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p41) := fun hu => hn (Or.inl hu)
  have u1 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p45 := by
    rcases h26831 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h17065 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)

theorem step28734 (p138 p189 p193 p262 p310 p864 p980 p983 p1055 p1061 p1325 p1349 : Prop)
    (h26903 : p983 ∨ p980)
    (h26845 : p193 ∨ p189)
    (h26909 : p1061 ∨ p1055)
    (h17646 : (¬ p138) ∨ (¬ p193) ∨ (¬ p262) ∨ (¬ p310) ∨ (¬ p864) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1325) ∨ (¬ p1349)) : (¬ p864) ∨ p980 ∨ (¬ p1349) ∨ p189 ∨ (¬ p1325) ∨ (¬ p310) ∨ (¬ p262) ∨ p1055 ∨ (¬ p138) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p980) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p189) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p1055) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p983 := by
    rcases h26903 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u10 : p193 := by
    rcases h26845 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u11 : p1061 := by
    rcases h26909 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h17646 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u10)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u11)
  · exact False.elim (q7 u4)
  · exact False.elim (q8 u2)

#print axioms step28734

end NineRUPTrial
